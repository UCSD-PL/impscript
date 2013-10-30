
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
    | _ -> failwith "lookupRetType"

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
  (* TODO *)
  | _ -> TAny

let joinTypes ts =
  Types.fold join ts TBot

let joinHeapEnvs he1 he2 =
  VarMap.fold (fun x pt2 acc ->
    if not (VarMap.mem x he2) then acc
    else let pt3 = VarMap.find x he2 in
         let (t2,t3) = (projTyp pt2, projTyp pt3) in
         VarMap.add x (Typ (join t2 t3)) acc
  ) he1 VarMap.empty

type ('a, 'b) result =
  | Ok of 'a * 'b
  | Err of 'a

let run foo args fError fOk =
  match foo args with
    | Err(a)  -> fError a
    | Ok(a,b) -> fOk a b

let errE s e       = Err (eTcErr s e)
let sTcErr s stmt  = sSeq [sExp (eTcErr s (eStr "")); stmt]
let errS s stmt    = Err (sTcErr s stmt)

(* TODO *)
let compatible s t =
  true

let coerce (e, s, t) =
  let (s1,s2) = (Printer.strTyp s, Printer.strTyp t) in
  if sub (s, t) then
    Ok (e, ())
  else if not !Settings.castInsertionMode then
    Err (eTcErr (spr "not a subtype:\n%s\n%s" s1 s2) e)
  else if compatible s t then
    Ok (eApp (eCast s t) [e], ())
  else
    Err (eTcErr (spr "not compatible:\n%s\n%s" s1 s2) e)

let rec tcExp (typeEnv, heapEnv, exp) = match exp.exp with

  | EBase(VNum _)  -> Ok (exp, (Typ tNum,   heapEnv, emptyOut))
  | EBase(VBool _) -> Ok (exp, (Typ tBool,  heapEnv, emptyOut))
  | EBase(VStr _)  -> Ok (exp, (Typ tStr,   heapEnv, emptyOut))
  | EBase(VUndef)  -> Ok (exp, (Typ tUndef, heapEnv, emptyOut))
  | EBase(VNull)   -> Ok (exp, (Typ tNull,  heapEnv, emptyOut))

  | EVarRead(x) ->
      (match lookupType x typeEnv with
        | None -> errE (spr "var [%s] isn't defined" x) exp
        | Some(Val(t))
        | Some(InvariantRef(t)) ->
            Ok (exp, (Typ t, heapEnv, addOutVar x emptyOut))
        | Some(StrongRef) ->
            (match lookupHeap x heapEnv with
              | None -> errE (spr "var [%s] is not in heap env" x) exp
              | Some(pt) -> Ok (exp, (pt, heapEnv, addOutVar x emptyOut))))

  | EFun(xs,body) when !Settings.castInsertionMode = false ->
      failwith "unannotated functions should not appear in checking mode"

  | EFun(xs,body) ->
      tcBareFun typeEnv heapEnv xs body

  | EAs({exp=EFun(xs,body)},Typ(TArrow(tArgs,tRet))) ->
      tcAnnotatedFun typeEnv heapEnv xs body Heap.empty tArgs tRet

  | EAs({exp=EFun(xs,body)},OpenArrow(h,tArgs,tRet)) ->
      tcAnnotatedFun typeEnv heapEnv xs body h tArgs tRet

  (* discard casts inserted in previous phase when compiling in this phase *)
  | EApp({exp=ECast(s,t)},eArgs) when !Settings.castInsertionMode ->
      (match eArgs with
        | [e1] ->
            run tcExp (typeEnv, heapEnv, e1)
              (fun e1 -> Err (eApp (eCast s t) [e1]))
              (fun e1 stuff -> Ok (e1, stuff))
        | _ ->
            failwith "casts should only have one argument")

  | ECast(s,t) ->
      if !Settings.castInsertionMode
      then failwith "cast should've been caught above"
      else Ok (exp, (Typ (TArrow ([s], t)), heapEnv, emptyOut))

  | EApp(eFun,eArgs) ->
      run tcExp (typeEnv, heapEnv, eFun)
        (fun eFun -> Err (eApp eFun eArgs))
        (fun eFun (ptFun,heapEnv,outFun) ->
           match ptFun with
            | OpenArrow _ ->
                Err (eApp (eTcErr "function has open type" eFun) eArgs)
            | Typ(TArrow(tArgs,tRet)) ->
                tcApp1 typeEnv heapEnv outFun eFun eArgs tArgs tRet
            | Typ(tFun) ->
                tcApp2 typeEnv heapEnv outFun eFun eArgs tFun)

  | EAs(_,_) ->
      errE "non-function value in ascription" exp

  | ETcErr _ ->
      failwith "tc ETcErr"

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

  run tcStmt (typeEnv, heapEnvFun, body)
    (fun body -> Err (eFun xs body))
    (fun body (ptBody,_,out) ->
       match ptBody with
        | OpenArrow _ ->
            Err (eFun xs (sTcErr "function body has an open type" body))
        | Typ(tBody) ->
            let tArgs = List.map (fun _ -> TAny) xs in
            let tRet = joinTypes (Types.add tBody out.retTypes) in
            let heap = Heap.filter (fun (x,_) -> Vars.mem x out.usedVars) heap in
            let arrow = ptArrow heap tArgs tRet in
            let out = { out with retTypes = Types.empty } in
            Ok (eAs (eFun xs body) arrow, (arrow, heapEnv, out)))

and tcAnnotatedFun typeEnv heapEnv xs body heap tArgs tRet =
  if List.length xs <> List.length tArgs
    then failwith "add handling for len(actuals) != len(formals)";
  let typeEnv = VarMap.add "@ret" (InvariantRef TAny) typeEnv in
  let (typeEnv,heapEnvFun) =
    List.fold_left (fun (acc1,acc2) (x,t) ->
      (VarMap.add x StrongRef acc1, VarMap.add x (Typ t) acc2)
    ) (typeEnv, VarMap.empty) (List.combine xs tArgs) in
  let typeEnv =
    Heap.fold
      (fun (x,t) acc -> VarMap.add x (InvariantRef t) acc) heap typeEnv in
  run tcStmt (typeEnv, heapEnvFun, body)
    (fun body -> Err (eFun xs body))
    (fun body (ptBody,_,_) ->
       match ptBody with
        | OpenArrow _ ->
            Err (eFun xs (sTcErr "function body has an open type" body))
        | Typ(tBody) ->
            let arrow = ptArrow heap tArgs tRet in
            if sub (tBody, tRet) then
              Ok (eAs (eFun xs body) arrow, (arrow, heapEnv, emptyOut))
            else
              Err (eFun xs (sTcErr "fun has bad fall-thru type" body)))

and tcApp1 typeEnv heapEnv outFun eFun eArgs tArgs tRet =
  if List.length eArgs <> List.length tArgs
    then failwith "add handling for len(actuals) != len(formals)";
  let obligations = List.combine eArgs tArgs in
  let (eArgs,maybeOutput) =
    List.fold_left (fun (eArgs,maybeOutput) (eArg,tArg) ->
      match maybeOutput with
       | None -> (eArgs @ [eArg], None)
       | Some(heapEnv,out) ->
           run tcCoerce (typeEnv, heapEnv, eArg, tArg)
             (fun eArg -> (eArgs @ [eArg], None))
             (fun eArg (heapEnv,out') ->
                let out = combineOut out out' in
                (eArgs @ [eArg], Some (heapEnv, out)))
    ) ([], Some (heapEnv, outFun)) obligations
  in
  (match maybeOutput with
    | None -> Err (eApp eFun eArgs)
    | Some(heapEnv,out) ->
        Ok (eApp eFun eArgs, (Typ tRet, heapEnv, out)))

and tcApp2 typeEnv heapEnv outFun eFun eArgs tFun =
  let tAnys = List.map (function _ -> TAny) eArgs in
  run coerce (eFun, tFun, TArrow (tAnys, TAny))
    (fun eFun -> Err (eApp eFun eArgs))
    (fun eFun () ->
       let (eArgs,maybeOutput) =
         List.fold_left (fun (eArgs,maybeOutput) eArg ->
           match maybeOutput with
            | None -> (eArgs @ [eArg], None)
            | Some(heapEnv,out) ->
                run tcExp (typeEnv, heapEnv, eArg)
                  (fun eArg -> (eArgs @ [eArg], None))
                  (fun eArg (_,heapEnv,out') ->
                     let out = combineOut out out' in
                     (eArg :: eArgs, Some (heapEnv, out)))
         ) ([], Some (heapEnv, outFun)) eArgs
       in
       (match maybeOutput with
         | None -> Err (eApp eFun eArgs)
         | Some(heapEnv,out) ->
             Ok (eApp eFun eArgs, (Typ TAny, heapEnv, out))))

and tcStmt ((typeEnv, heapEnv, stmt) as args) = match stmt.stmt with

  | SReturn(e) | SVarAssign(_,e)
    when isLambda e && !Settings.castInsertionMode = true ->
      begin match maybeCloseSomeVars heapEnv stmt with
        | Some(stmt) -> tcStmt (typeEnv, heapEnv, stmt)
        | None       -> _tcStmt args
      end

  | _ -> _tcStmt args

and _tcStmt (typeEnv, heapEnv, stmt) = match stmt.stmt with

  | SExp(e) ->
      run tcExp (typeEnv, heapEnv, e)
        (fun e -> Err (sExp e))
        (fun e (pt,heapEnv,out) -> Ok (sExp e, (pt, heapEnv, out)))

  | SReturn(e) ->
      run tcExp (typeEnv, heapEnv, e)
        (fun e -> Err (sRet e))
        (fun e (pt,heapEnv,out) ->
           match pt with
            | OpenArrow _ ->
                Err (sTcErr "return expression has an open type" (sRet e))
            | Typ(t) ->
                let tExpected = lookupRetType typeEnv in
                run coerce (e, t, tExpected)
                   (fun e -> Err (sRet e))
                   (fun e () ->
                      Ok (sRet e, (Typ TBot, heapEnv, addOutRet t out))))

  | SVarDecl(x,s) ->
      if VarMap.mem x typeEnv
      then errS (spr "var [%s] is already scope" x) stmt
      else begin
        let typeEnv = VarMap.add x StrongRef typeEnv in
        let heapEnv = VarMap.add x (Typ (TBase TUndef)) heapEnv in
        run tcStmt (typeEnv, heapEnv, s)
          (fun s -> Err (wrapStmt (SVarDecl (x, s))))
          (fun s (pt,heapEnv,out) ->
             let heapEnv = VarMap.remove x heapEnv in (* TODO not checking *)
             Ok (sLetRef x s, (pt, heapEnv, out)))
      end

  | SVarAssign(x,e) ->
      begin match lookupType x typeEnv with
        | None -> errS (spr "var [%s] isn't defined" x) stmt
        | Some(Val _) -> errS (spr "val [%s] is not assignable" x) stmt
        | Some(InvariantRef(t)) ->
            run tcCoerce (typeEnv, heapEnv, e, t)
              (fun e -> Err (sAssign x e))
              (fun e (heapEnv,out) -> Ok (sAssign x e, (Typ t, heapEnv, out)))
        | Some(StrongRef) ->
            run tcExp (typeEnv, heapEnv, e)
              (fun e -> Err (sAssign x e))
              (fun e (pt,heapEnv,out) ->
                 let heapEnv = VarMap.add x pt heapEnv in
                 Ok (sAssign x e, (pt, heapEnv, out)))
      end
        

  | SSeq(s1,s2) ->
      run tcStmt (typeEnv, heapEnv, s1)
        (fun s1 -> Err (sSeq [s1; s2]))
        (fun s1 (pt1,heapEnv1,out1) ->
           if pt1 = Typ TBot then Ok (sSeq [s1; s2], (pt1, heapEnv1, out1))
           else run tcStmt (typeEnv, heapEnv1, s2)
                  (fun s2 -> Err (sSeq [s1; s2]))
                  (fun s2 (pt2,heapEnv2,out2) ->
                     let out = combineOut out1 out2 in
                     Ok (sSeq [s1; s2], (pt2, heapEnv2, out))))

  | SIf(e1,s2,s3) ->
      (* requiring boolean guard for now *)
      run tcCoerce (typeEnv, heapEnv, e1, tBool)
        (fun e1 -> Err (sIf e1 s2 s3))
        (fun e1 (heapEnv,out1) -> run tcStmt (typeEnv, heapEnv, s2)
           (fun s2 -> Err (sIf e1 s2 s3))
           (fun s2 (ptThen,heapEnv2,out2) -> run tcStmt (typeEnv, heapEnv, s3)
              (fun s3 -> Err (sIf e1 s2 s3))
              (fun s3 (ptElse,heapEnv3,out3) ->
                 let (tThen,tElse) = (projTyp ptThen, projTyp ptElse) in
                 let tJoin = join tThen tElse in
                 let hJoin = joinHeapEnvs heapEnv2 heapEnv3 in
                 let out = List.fold_left combineOut out1 [out2; out3] in
                 Ok (sIf e1 s2 s3, (Typ tJoin, hJoin, out)))))

  | SWhile _ -> failwith "tc while"

  | SVarInvariant(x,tGoalX,s) ->
      (match lookupHeap x heapEnv with
        | None -> failwith (spr "varinvariant var [%s] not found" x)
        | Some(OpenArrow _) -> failwith "varinvar open"
        | Some(Typ(tCurrentX)) ->
            if not (sub (tCurrentX, tGoalX)) then
              (* could allow coercion in the bad case instead *)
              let str = spr "varinvariant var [%s]: bad subtyping" x in
              Err (sInvar x tGoalX (sTcErr str s))
            else (* shadow x in type environment *)
              let typeEnv = VarMap.add x (InvariantRef tGoalX) typeEnv in
              let heapEnv = VarMap.remove x heapEnv in
              run tcStmt (typeEnv, heapEnv, s)
                (fun s -> Err (sInvar x tGoalX s))
                (fun s stuff -> Ok (sInvar x tGoalX s, stuff)))

  | SClose(xs,s) ->
      let (rely,guarantee) =
        List.fold_left (fun (accR,accG) x ->
          match lookupType x typeEnv with
           | Some(StrongRef) ->
               (match lookupHeap x heapEnv with
                 | Some(OpenArrow(h,tArgs,tRet)) ->
                     let accR = Heap.union accR h in
                     let accG = Heap.add (x, TArrow (tArgs, tRet)) accG in
                     (accR, accG)
                 | Some(Typ _) -> failwith (spr "[%s] is not open func" x)
                 | None -> failwith "sclose 1")
           | _ -> failwith "sclose 2"
        ) (Heap.empty, Heap.empty) xs
      in
      if not (Heap.equal rely guarantee) then
        Err (sClose xs (sTcErr "Rely != Guarantee" s))
      else
        let (typeEnv,heapEnv) =
          Heap.fold (fun (x,t) (acc1,acc2) ->
            (VarMap.add x (Val t) acc1, VarMap.remove x acc2)
          ) rely (typeEnv, heapEnv)
        in
        run tcStmt (typeEnv, heapEnv, s)
          (fun s -> Err (sClose xs s))
          (fun s stuff -> Ok (sClose xs s, stuff))

  | SLoadedSrc(f,s) ->
      run tcStmt (typeEnv, heapEnv, s)
        (fun s -> Err (wrapStmt (SLoadedSrc (f, s))))
        (fun s stuff -> Ok (wrapStmt (SLoadedSrc (f, s)), stuff))

  | SExternVal(x,tx,s) ->
      let typeEnv = VarMap.add x (Val tx) typeEnv in
      run tcStmt (typeEnv, heapEnv, s)
        (fun s -> Err (wrapStmt (SExternVal (x, tx, s))))
        (fun s stuff -> Ok (wrapStmt (SExternVal (x, tx, s)), stuff))

and tcCoerce (typeEnv, heapEnv, e, tGoal) =
  run tcExp (typeEnv, heapEnv, e)
    (fun e -> Err e)
    (fun e (pt,heapEnv,out) ->
       match pt with
        | OpenArrow _ -> errE "cannot coerce from open arrow" e
        | Typ(t) ->
            run coerce (e, t, tGoal)
              (fun e -> Err e)
              (fun e () -> Ok (e, (heapEnv, out))))

let typecheck prog =
  match tcStmt (VarMap.empty, VarMap.empty, prog) with
   | Ok(prog,(_,_,_)) -> Ok (prog, ())
   | Err(prog)        -> Err prog
