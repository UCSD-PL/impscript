
open Lang
open LangUtils

type more_outputs = { retTypes: Types.t; usedVars: Vars.t }

let emptyOut =
  { retTypes = Types.empty;
    usedVars = Vars.empty
  }

let combineOut o1 o2 =
  { retTypes = Types.union o1.retTypes o2.retTypes;
    usedVars = Vars.union o1.usedVars o2.usedVars
  }

let addOutRet t o =
  { o with retTypes = Types.add t o.retTypes}

let addOutVar x o =
  { o with usedVars = Vars.add x o.usedVars}

let lookupType x typeEnv =
  if VarMap.mem x typeEnv then Some (VarMap.find x typeEnv) else None

let lookupHeap x heapEnv =
  if VarMap.mem x heapEnv then Some (VarMap.find x heapEnv) else None

let lookupRetType typeEnv =
  match lookupType "@ret" typeEnv with
    | Some(InvariantRef(t)) -> t
    | _ -> failwith "lookupRetType strong"

let isLambda exp = match exp.exp with
  | EFun _ | EAs({exp=EFun _},_) -> true
  | _ -> false

let maybeCloseSomeVars heapEnv stmt =
  VarMap.fold (fun x pt acc ->
    match pt, acc with
      | Typ(TBase(TUndef)), _
      | OpenArrow _, _  -> acc
      | Typ(t), None    -> Some (wrapStmt (SVarInvariant (x, t, stmt)))
      | Typ(t), Some(s) -> Some (wrapStmt (SVarInvariant (x, t, s)))
  ) heapEnv None

let projTyp = function
  | OpenArrow _ -> failwith "projTyp"
  | Typ(t) -> t

let sub = function
  | s, t when s = t -> true
  | TBot, _ -> true
  | _, TAny -> true
  | s, TUnion ts when List.mem s ts -> true
  (* TODO *)
  | _ -> false

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

  | EBase(VNum _)  -> (exp, Typ tNum,   heapEnv, emptyOut)
  | EBase(VBool _) -> (exp, Typ tBool,  heapEnv, emptyOut)
  | EBase(VStr _)  -> (exp, Typ tStr,   heapEnv, emptyOut)
  | EBase(VUndef)  -> (exp, Typ tUndef, heapEnv, emptyOut)
  | EBase(VNull)   -> (exp, Typ tNull,  heapEnv, emptyOut)

  | EVarRead(x) ->
      begin match lookupType x typeEnv with
        | None -> failwith (spr "reading var [%s] that isn't defined" x)
        | Some(Val(t)) -> (exp, Typ t, heapEnv, addOutVar x emptyOut)
        | Some(InvariantRef(t)) -> (exp, Typ t, heapEnv, addOutVar x emptyOut)
        | Some(StrongRef) ->
            begin match lookupHeap x heapEnv with
              | None -> failwith (spr "var [%s] isn't in heap env" x)
              | Some(pt) -> (exp, pt, heapEnv, addOutVar x emptyOut)
            end
      end

  | EFun(xs,body) when !Settings.castInsertionMode = false ->
      failwith "unannotated functions should not appear in checking mode"

  | EFun(xs,body) ->
      tcBareFun typeEnv heapEnv xs body

  | EAs({exp=EFun(xs,body)},Typ(TArrow(tArgs,tRet))) ->
      tcAnnotatedFun typeEnv heapEnv xs body Heap.empty tArgs tRet

  | EAs({exp=EFun(xs,body)},OpenArrow(h,tArgs,tRet)) ->
      tcAnnotatedFun typeEnv heapEnv xs body h tArgs tRet

  (* discard casts inserted in previous phase when compiling in this phase *)
  | EApp({exp=ECast _},eArgs) when !Settings.castInsertionMode ->
      begin match eArgs with
        | [e1] -> tcExp typeEnv heapEnv e1
        | _ -> failwith "casts should only have one argument"
      end

  | ECast(s,t) ->
      if !Settings.castInsertionMode
      then failwith "cast should've been caught above"
      else (exp, Typ (TArrow ([s], t)), heapEnv, emptyOut)

  | EApp(eFun,eArgs) ->
      let (eFun,ptFun,heapEnv,out) = tcExp typeEnv heapEnv eFun in
      begin match ptFun with
        | OpenArrow _ -> failwith "EApp openarrow"
        | Typ(TArrow(tArgs,tRet)) ->
            let _ =
              if List.length eArgs <> List.length tArgs
              then failwith "add handling for len(actuals) != len(formals)" in
            let obligations = List.combine eArgs tArgs in
            let (eArgs,heapEnv,out) =
              List.fold_left (fun (eArgs,heapEnv,out) (eArg,tExpected) ->
                let (eArg,heapEnv,out') =
                  tcCoerce typeEnv heapEnv eArg tExpected in
                (eArg :: eArgs, heapEnv, combineOut out out')
              ) ([], heapEnv, out) obligations
            in
            (eApp eFun (List.rev eArgs), Typ tRet, heapEnv, out)
        | Typ(tFun) ->
            let tAnys = List.map (function _ -> TAny) eArgs in
            let eFun = coerce eFun tFun (TArrow (tAnys, TAny)) in
            let (eArgs,heapEnv,out) =
              List.fold_left (fun (eArgs,heapEnv,out) eArg ->
                let (eArg,_,heapEnv,out') = tcExp typeEnv heapEnv eArg in
                (eArg :: eArgs, heapEnv, combineOut out out')
              ) ([], heapEnv, out) eArgs
            in
            (eApp eFun (List.rev eArgs), Typ TAny, heapEnv, out)
      end

  | EAs(e,_) ->
      (* let _ = tcExp typeEnv heapEnv e in *)
      failwith (spr "tcExp EAs: non-function value\n%s"
        (Printer.strExpAst e))

and tcBareFun typeEnv heapEnv xs body =

  let typeEnv = VarMap.add "@ret" (InvariantRef TAny) typeEnv in
  let (typeEnv,heapEnvFun) =
    List.fold_left (fun (acc1,acc2) x ->
      (VarMap.add x StrongRef acc1, VarMap.add x (Typ TAny) acc2)
    ) (typeEnv, VarMap.empty) xs in

  (* eagerly add all strong assignables to function's input heap env.
     then after type checking the function, synthesize an open arrow
     with all of these variables that were used at least once. *)
  let (heap,heapEnvFun) =
    VarMap.fold (fun x pt (acc1,acc2) ->
      match pt with
        | Typ(t) -> (Heap.add (x,t) acc1, VarMap.add x (Typ t) acc2)
        | OpenArrow(_,tArgs,tRet) ->
            let tArrow = TArrow (tArgs, tRet) in
            (Heap.add (x,tArrow) acc1, VarMap.add x (Typ tArrow) acc2)
    ) heapEnv (Heap.empty, heapEnvFun) in

  let (body,ptBody,_,out) = tcStmt typeEnv heapEnvFun body in
  begin match ptBody with
    | OpenArrow _ -> failwith "bare EFun ptBody"
    | Typ(tBody) ->
        let tArgs = List.map (fun _ -> TAny) xs in
        let tRet = List.fold_left join tBody (Types.elements out.retTypes) in
        let heap = Heap.filter (fun (x,_) -> Vars.mem x out.usedVars) heap in
        let arrow = ptArrow heap tArgs tRet in
        let out = { out with retTypes = Types.empty } in
        (eAs (eFun xs body) arrow, arrow, heapEnv, out)
  end

and tcAnnotatedFun typeEnv heapEnv xs body heap tArgs tRet =
  let _ =
    if List.length xs <> List.length tArgs
    then failwith "add handling for len(actuals) != len(formals)" in
  let typeEnv = VarMap.add "@ret" (InvariantRef TAny) typeEnv in
  let (typeEnv,heapEnvFun) =
    List.fold_left (fun (acc1,acc2) (x,t) ->
      (VarMap.add x StrongRef acc1, VarMap.add x (Typ t) acc2)
    ) (typeEnv, VarMap.empty) (List.combine xs tArgs) in
  let typeEnv =
    Heap.fold
      (fun (x,t) acc -> VarMap.add x (InvariantRef t) acc) heap typeEnv in
  let (body,ptBody,_,_) = tcStmt typeEnv heapEnvFun body in
  begin match ptBody with
    | OpenArrow _ -> failwith "annotated EFun ptBody"
    | Typ(tBody) ->
        let arrow = ptArrow heap tArgs tRet in
        if sub (tBody, tRet)
        then (eAs (eFun xs body) arrow, arrow, heapEnv, emptyOut)
        else failwith "annotated fun has bad fall-thru type"
  end

and tcStmt typeEnv heapEnv stmt = match stmt.stmt with

  | SReturn(e) | SVarAssign(_,e)
    when isLambda e && !Settings.castInsertionMode = true ->
      begin match maybeCloseSomeVars heapEnv stmt with
        | Some(stmt') -> tcStmt typeEnv heapEnv stmt'
        | None        -> _tcStmt typeEnv heapEnv stmt
      end

  | _ -> _tcStmt typeEnv heapEnv stmt

and _tcStmt typeEnv heapEnv stmt = match stmt.stmt with

  | SExp(e) ->
      let (e,pt,heapEnv,out) = tcExp typeEnv heapEnv e in
      (sExp e, pt, heapEnv, out)

  | SReturn(e) ->
      let (e,pt,heapEnv,out) = tcExp typeEnv heapEnv e in
      begin match pt with
        | OpenArrow _ -> failwith "SReturn type is open"
        | Typ(t) ->
            let tExpected = lookupRetType typeEnv in
            let e = coerce e t tExpected in
            (sRet e, Typ TBot, heapEnv, addOutRet t out)
      end
      
  | SVarDecl(x,s) ->
      if VarMap.mem x typeEnv then failwith (spr "var [%s] is already scope" x)
      else
        let (s,pt,heapEnv1,out) =
          tcStmt (VarMap.add x StrongRef typeEnv)
             (VarMap.add x (Typ (TBase TUndef)) heapEnv) s in
        let heapEnv = VarMap.remove x heapEnv1 in (* TODO not checking *)
        (sLetRef x s, pt, heapEnv, out)

  | SVarAssign(x,e) ->
      begin match lookupType x typeEnv with
        | None -> failwith (spr "assigning to var [%s] that isn't defined" x)
        | Some(Val _) -> failwith (spr "can't assign to immutable var [%s]" x)
        | Some(InvariantRef(t)) ->
            let (e,heapEnv,out) = tcCoerce typeEnv heapEnv e t in
            (sAssign x e, Typ t, heapEnv, out)
        | Some(StrongRef) ->
            let (e,pt,heapEnv,out) = tcExp typeEnv heapEnv e in
            let heapEnv = VarMap.add x pt heapEnv in
            (sAssign x e, pt, heapEnv, out)
      end
        
  | SSeq(s1,s2) ->
      let (s1,pt1,heapEnv1,out1) = tcStmt typeEnv heapEnv s1 in
      let (s2,pt2,heapEnv2,out2) = tcStmt typeEnv heapEnv1 s2 in
      let pt = if pt1 = Typ TBot then pt1 else pt2 in
      (sSeq [s1;s2], pt, heapEnv2, combineOut out1 out2)

  | SIf(e1,s2,s3) ->
      (* requiring boolean guard for now *)
      let (e1,heapEnv,out1) = tcCoerce typeEnv heapEnv e1 tBool in
      let (s2,ptThen,heapEnv2,out2) = tcStmt typeEnv heapEnv s2 in
      let (s3,ptElse,heapEnv3,out3) = tcStmt typeEnv heapEnv s3 in
      let heapEnv23 = (* throw away var decls on the branches *)
        VarMap.fold (fun x pt2 acc ->
          if not (VarMap.mem x heapEnv3) then acc
          else let pt3 = VarMap.find x heapEnv3 in
               let (t2,t3) = (projTyp pt2, projTyp pt3) in
               VarMap.add x (Typ (join t2 t3)) acc) heapEnv2 VarMap.empty
      in
      let out = List.fold_left combineOut out1 [out2; out3] in
      let (tThen,tElse) = (projTyp ptThen, projTyp ptElse) in
      (sIf e1 s2 s3, Typ (join tThen tElse), heapEnv23, out)

  | SWhile _ -> failwith "tc while"

  | SVarInvariant(x,tGoalX,s) ->
      begin match lookupHeap x heapEnv with
        | None -> failwith (spr "varinvariant var [%s] not found" x)
        | Some(OpenArrow _) -> failwith "varinvar open"
        | Some(Typ(tCurrentX)) ->
            if not (sub (tCurrentX, tGoalX))
            then failwith (spr "varinvariant var [%s]: bad subtyping" x)
                 (* could allow coercion in the bad case instead *)
            else (* shadow x in type environment *)
              let typeEnv = VarMap.add x (InvariantRef tGoalX) typeEnv in
              let heapEnv = VarMap.remove x heapEnv in
              let (s,pt,heapEnv,out) = tcStmt typeEnv heapEnv s in
              (wrapStmt (SVarInvariant (x, tGoalX, s)), pt, heapEnv, out)
      end

  | SClose(xs,s) ->
      let (rely,guarantee) =
        List.fold_left (fun (accR,accG) x ->
          match lookupType x typeEnv with
            | Some(StrongRef) ->
                begin match lookupHeap x heapEnv with
                  | Some(OpenArrow(h,tArgs,tRet)) ->
                      let accR = Heap.union accR h in
                      let accG = Heap.add (x, TArrow (tArgs, tRet)) accG in
                      (accR, accG)
                  | Some(Typ _) -> failwith (spr "[%s] is not open func" x)
                  | None -> failwith "sclose 1"
                end
            | _ -> failwith "sclose 2"
        ) (Heap.empty, Heap.empty) xs in
      if not (Heap.equal rely guarantee) then failwith "SClose rely guarantee"
      else
        let (typeEnv,heapEnv) =
          Heap.fold (fun (x,t) (acc1,acc2) ->
            (VarMap.add x (InvariantRef t) acc1, VarMap.remove x acc2)
          ) rely (typeEnv, heapEnv) in
        let (s,pt,heapEnv,out) = tcStmt typeEnv heapEnv s in
        (wrapStmt (SClose (xs, s)), pt, heapEnv, out)

  | SLoadedSrc(f,s) ->
      let (s,pt,heapEnv,out) = tcStmt typeEnv heapEnv s in
      (wrapStmt (SLoadedSrc (f, s)), pt, heapEnv, out)

  | SExternVal(x,tx,s) ->
      let typeEnv = VarMap.add x (Val tx) typeEnv in
      let (s,pt,heapEnv,out) = tcStmt typeEnv heapEnv s in
      (wrapStmt (SExternVal (x, tx, s)), pt, heapEnv, out)

and tcCoerce typeEnv heapEnv e tGoal =
  let (e,pt,heapEnv,out) = tcExp typeEnv heapEnv e in
  match pt with
    | OpenArrow _ -> failwith "tcCoerce open arrow"
    | Typ(t) ->
        let e = coerce e t tGoal in
        (e, heapEnv, out)

let typecheck prog =
  let (prog,_,_,_) = tcStmt VarMap.empty VarMap.empty prog in
  prog
