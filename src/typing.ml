
open Lang
open LangUtils

let lookupType x typeEnv =
  if VarMap.mem x typeEnv then Some (VarMap.find x typeEnv) else None

let lookupHeap x heapEnv =
  if VarMap.mem x heapEnv then Some (VarMap.find x heapEnv) else None

let lookupRetType typeEnv =
  match lookupType "@ret" typeEnv with
    | Some(InvariantRef(t)) -> t
    | _ -> failwith "lookupRetType strong"

let needToCloseVars heapEnv exceptedVars e =
  let isLambda exp = match exp.exp with
    | EFun _ | EAs({exp=EFun _},TArrow _) -> true
    | _ -> false
  in
  isLambda e && VarMap.exists (fun x _ -> not (List.mem x exceptedVars)) heapEnv
  (* TODO for these exceptedVars, maybe they should appear as Vals so they
     cannot be written to during the body *)

let closeVars heapEnv exceptedVars stmt =
  VarMap.fold (fun x t acc ->
    if List.mem x exceptedVars then acc
    else wrapStmt (SVarInvariant (x, t, acc))
  ) heapEnv stmt

let sub = function
  | s, t when s = t -> true
  | TBot, _ -> true
  | _, TAny -> true
  | s, TUnion ts when List.mem s ts -> true
  (* TODO *)
  | _ -> false

let tUnion ts = TUnion (Utils.removeDupes ts)

let join s t = match s, t with
  | s, t when s = t -> s
  | _, TAny | TAny, _ -> TAny
  | u, TBot | TBot, u -> u
  | TBase _, TBase _ -> tUnion [s; t]
  | TUnion l1, TUnion l2 -> tUnion (l1 @ l2)
  | TUnion l, u | u, TUnion l -> tUnion (u :: l)
  | _ -> failwith (spr "join [%s] [%s]" (Printer.strTyp s) (Printer.strTyp t))

let coerce e s t =
  if sub (s, t) then e
  else if !Settings.castInsertionMode then
    (* TODO check compatibility *)
    wrapExp (EApp (wrapExp (ECast (s, t)), [e]))
  else
    failwith (spr "castMode is false: %s %s"
      (Printer.strTyp s) (Printer.strTyp t))

let rec tcExp typeEnv heapEnv exp = match exp.exp with

  | EBase(VNum _)  -> (exp, tNum,   heapEnv, Types.empty)
  | EBase(VBool _) -> (exp, tBool,  heapEnv, Types.empty)
  | EBase(VStr _)  -> (exp, tStr,   heapEnv, Types.empty)
  | EBase(VUndef)  -> (exp, tUndef, heapEnv, Types.empty)
  | EBase(VNull)   -> (exp, tNull,  heapEnv, Types.empty)

  | EVarRead(x) ->
      begin match lookupType x typeEnv with
        | None -> failwith (spr "reading var [%s] that isn't defined" x)
        | Some(Val(t)) -> (exp, t, heapEnv, Types.empty)
        | Some(InvariantRef(t)) -> (exp, t, heapEnv, Types.empty)
        | Some(StrongRef) ->
            begin match lookupHeap x heapEnv with
              | None -> failwith (spr "var [%s] isn't in heap env" x)
              | Some(t) -> (exp, t, heapEnv, Types.empty)
            end
      end

  | EFun(xs,body) ->
      let typeEnv =
        List.fold_left (fun acc x -> VarMap.add x StrongRef acc)
          (VarMap.add "@ret" (InvariantRef TAny) typeEnv) xs in
      let heapEnvFun =
        List.fold_left (fun acc x -> VarMap.add x TAny acc) 
          VarMap.empty xs in
      let (body,tBody,_,retTypes) = tcStmt typeEnv heapEnvFun body in
      let tArgs = List.map (fun _ -> TAny) xs in
      (* using tBody, rather than tUndef, since, from ESeq, it might be TBot *)
      let tRet = List.fold_left join tBody (Types.elements retTypes) in
      let tArrow = TArrow (tArgs, tRet) in
      (eAs (eFun xs body) tArrow, tArrow, heapEnv, Types.empty)

  | EAs({exp=EFun(xs,body)},(TArrow(tArgs,tRet) as tArrow)) ->
      let _ =
        if List.length xs <> List.length tArgs
        then failwith "add handling for len(actuals) != len(formals)" in
      let typeEnv =
        List.fold_left (fun acc x -> VarMap.add x StrongRef acc)
          (VarMap.add "@ret" (InvariantRef TAny) typeEnv) xs in
      let heapEnvFun =
        List.fold_left (fun acc (x,t) -> VarMap.add x t acc) 
          VarMap.empty (List.combine xs tArgs) in
      let (body,tBody,_,_) = tcStmt typeEnv heapEnvFun body in
      if sub (tBody, tRet)
      then (eAs (eFun xs body) tArrow, tArrow, heapEnv, Types.empty)
      else failwith "annotated fun has bad fall-thru type: "

  | EApp(eFun,eArgs) ->
      let (eFun,tFun,heapEnv,retTypes) = tcExp typeEnv heapEnv eFun in
      begin match tFun with
        | TArrow(tArgs,tRet) ->
            let _ =
              if List.length eArgs <> List.length tArgs
              then failwith "add handling for len(actuals) != len(formals)" in
            let obligations = List.combine eArgs tArgs in
            let (eArgs,heapEnv,retTypes) =
              List.fold_left (fun (eArgs,heapEnv,retTypes) (eArg,tExpected) ->
                let (eArg,heapEnv,ret) =
                  tcCoerce typeEnv heapEnv eArg tExpected in
                (eArg :: eArgs, heapEnv, Types.union ret retTypes)
              ) ([], heapEnv, retTypes) obligations
            in
            (eApp eFun (List.rev eArgs), tRet, heapEnv, retTypes)
        | _ ->
            let tAnys = List.map (function _ -> TAny) eArgs in
            let eFun = coerce eFun tFun (TArrow (tAnys, TAny)) in
            let (eArgs,heapEnv,retTypes) =
              List.fold_left (fun (eArgs,heapEnv,retTypes) eArg ->
                let (eArg,_,heapEnv,ret) = tcExp typeEnv heapEnv eArg in
                (eArg :: eArgs, heapEnv, Types.union ret retTypes)
              ) ([], heapEnv, retTypes) eArgs
            in
            (eApp eFun (List.rev eArgs), TAny, heapEnv, retTypes)
      end

  | EAs(e,t) ->
      let _ = tcExp typeEnv heapEnv e in
      failwith "tcExp EAs: non-function value"

  | ECast(s,t) ->
      if !Settings.castInsertionMode
      then failwith "cast should've been discarded by parser in insertion mode"
      else (exp, TArrow ([s], t), heapEnv, Types.empty)

and tcStmt typeEnv heapEnv stmt = match stmt.stmt with

  | SExp(e) ->
      let (e,t,heapEnv,ret) = tcExp typeEnv heapEnv e in
      (sExp e, t, heapEnv, ret)

  | SReturn(e) when needToCloseVars heapEnv [] e ->
      tcStmt typeEnv heapEnv (closeVars heapEnv [] stmt)

  | SReturn(e) ->
      let tExpected = lookupRetType typeEnv in
      let (e,s,heapEnv,ret) = tcExp typeEnv heapEnv e in
      let e = coerce e s tExpected in
      (sRet e, TBot, heapEnv, Types.add s ret)
      
  | SVarDecl(x,s) ->
      if VarMap.mem x typeEnv then failwith (spr "var [%s] is already scope" x)
      else
        let (s,t,heapEnv1,ret) =
          tcStmt (VarMap.add x StrongRef typeEnv)
             (VarMap.add x (TBase TUndef) heapEnv) s in
        let heapEnv = VarMap.remove x heapEnv1 in (* TODO not checking *)
        (sLetRef x s, t, heapEnv, ret)

  | SVarAssign(x,e) when needToCloseVars heapEnv [x] e ->
      tcStmt typeEnv heapEnv (closeVars heapEnv [x] stmt)

  | SVarAssign(x,e) ->
      begin match lookupType x typeEnv with
        | None -> failwith (spr "assigning to var [%s] that isn't defined" x)
        | Some(Val _) -> failwith (spr "can't assign to immutable var [%s]" x)
        | Some(InvariantRef(t)) ->
            let (e,heapEnv,ret) = tcCoerce typeEnv heapEnv e t in
            (sAssign x e, t, heapEnv, ret)
        | Some(StrongRef) ->
            let (e,t,heapEnv,ret) = tcExp typeEnv heapEnv e in
            let heapEnv = VarMap.add x t heapEnv in
            (sAssign x e, t, heapEnv, ret)
      end
        
  | SSeq(s1,s2) ->
      let (s1,t1,heapEnv1,ret1) = tcStmt typeEnv heapEnv s1 in
      let (s2,t2,heapEnv2,ret2) = tcStmt typeEnv heapEnv1 s2 in
      let t = if t1 = TBot then TBot else t2 in
      (sSeq [s1;s2], t, heapEnv2, Types.union ret1 ret2)

  | SIf(e1,s2,s3) ->
      (* requiring boolean guard for now *)
      let (e1,heapEnv,ret1) = tcCoerce typeEnv heapEnv e1 tBool in
      let (s2,t2,heapEnv2,ret2) = tcStmt typeEnv heapEnv s2 in
      let (s3,t3,heapEnv3,ret3) = tcStmt typeEnv heapEnv s3 in
      let heapEnv23 = (* throw away var decls on the branches *)
        VarMap.fold (fun x t2 acc ->
          if not (VarMap.mem x heapEnv3) then acc
          else let t3 = VarMap.find x heapEnv3 in
               VarMap.add x (join t2 t3) acc) heapEnv2 VarMap.empty
      in
      let ret = List.fold_left Types.union ret1 [ret2; ret3] in
      (sIf e1 s2 s3, join t2 t3, heapEnv23, ret)

  | SWhile _ -> failwith "tc while"

  | SVarInvariant(x,tGoalX,s) ->
      begin match lookupHeap x heapEnv with
        | None -> failwith (spr "varinvariant var [%s] not found" x)
        | Some(tCurrentX) ->
            if not (sub (tCurrentX, tGoalX))
            then failwith (spr "varinvariant var [%s]: bad subtyping" x)
                 (* could allow coercion in the bad case instead *)
            else (* shadow x in type environment *)
              let typeEnv = VarMap.add x (InvariantRef tGoalX) typeEnv in
              let heapEnv = VarMap.remove x heapEnv in
              let (s,t,heapEnv,ret) = tcStmt typeEnv heapEnv s in
              (wrapStmt (SVarInvariant (x, tGoalX, s)), t, heapEnv, ret)
      end

  | SLoadedSrc(f,s) ->
      let (s,t,heapEnv,ret) = tcStmt typeEnv heapEnv s in
      (wrapStmt (SLoadedSrc (f, s)), t, heapEnv, ret)

  | SExternVal(x,tx,s) ->
      let typeEnv = VarMap.add x (Val tx) typeEnv in
      let (s,t,heapEnv,ret) = tcStmt typeEnv heapEnv s in
      (wrapStmt (SExternVal (x, tx, s)), t, heapEnv, ret)

and tcCoerce typeEnv heapEnv e tGoal =
  let (e,t,heapEnv,ret) = tcExp typeEnv heapEnv e in
  let e = coerce e t tGoal in
  (e, heapEnv, ret)

let typecheck prog =
  let (prog,_,_,_) = tcStmt VarMap.empty VarMap.empty prog in
  prog
