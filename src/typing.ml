
open Lang
open LangUtils

type type_env_binding =
  | Val of typ
  | StrongRef
  | InvariantRef of typ

module TypeEnv = struct

  type t = { bindings: type_env_binding VarMap.t; loc_vars: Vars.t; }

  let empty : t =
    { bindings = VarMap.empty; loc_vars = Vars.empty }

  let lookupType : var -> t -> type_env_binding option =
  fun x typeEnv ->
    if VarMap.mem x typeEnv.bindings
    then Some (VarMap.find x typeEnv.bindings)
    else None

  let lookupRetType : t -> typ =
  fun typeEnv ->
    match lookupType "@ret" typeEnv with
      | Some(InvariantRef(t)) -> t
      | _ -> failwith "lookupRetType"

  let memVar : var -> t -> bool =
  fun x typeEnv ->
    VarMap.mem x typeEnv.bindings

  let addVar : var -> type_env_binding -> t -> t =
  fun x y typeEnv ->
    { typeEnv with bindings = VarMap.add x y typeEnv.bindings }

  let addLocationVariable : var -> t -> t=
  fun x typeEnv ->
    { typeEnv with loc_vars = Vars.add x typeEnv.loc_vars }

end

module HeapEnv = struct

  type t = { vars: pre_type VarMap.t; locs: recd_type LocMap.t; }

  let empty : t =
    { vars = VarMap.empty; locs = LocMap.empty }

  let addVar : var -> pre_type -> t -> t =
  fun x pt he ->
    { he with vars = VarMap.add x pt he.vars }

  let lookupVar : var -> t -> pre_type option =
  fun x heapEnv ->
    if VarMap.mem x heapEnv.vars
    then Some (VarMap.find x heapEnv.vars)
    else None

  let removeVar : var -> t -> t =
  fun x he ->
    { he with vars = VarMap.remove x he.vars }

  let addLoc : loc -> recd_type -> t -> t =
  fun l rt he ->
    { he with locs = LocMap.add l rt he.locs }

  let lookupLoc : loc -> t -> recd_type option =
  fun l heapEnv ->
    if LocMap.mem l heapEnv.locs
    then Some (LocMap.find l heapEnv.locs)
    else None

  let removeLoc : loc -> t -> t =
  fun l he ->
    { he with locs = LocMap.remove l he.locs }

  let equal : t -> t -> bool =
  fun he1 he2 ->
    let cmp x y = compare x y = 0 in
    VarMap.equal cmp he1.vars he2.vars && LocMap.equal cmp he1.locs he2.locs

end

module MoreOut = struct

  type t = { retTypes: Types.t; usedVars: Vars.t }

  let empty : t =
    { retTypes = Types.empty; usedVars = Vars.empty }

  let combine : t -> t -> t =
  fun o1 o2 ->
    { retTypes = Types.union o1.retTypes o2.retTypes;
      usedVars = Vars.union o1.usedVars o2.usedVars
    }

  let addRetType : typ -> t -> t =
  fun t o ->
    { o with retTypes = Types.add t o.retTypes}

  let addUsedVar : var -> t -> t =
  fun x o ->
    { o with usedVars = Vars.add x o.usedVars}

end

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

let joinTypes : Types.t -> typ =
fun ts ->
  Types.fold join ts TBot

let joinHeapEnvs : HeapEnv.t -> HeapEnv.t -> HeapEnv.t =
  let joinVars he1 he2 =
    VarMap.fold (fun x pt2 acc ->
      if not (VarMap.mem x he2) then acc
      else let pt3 = VarMap.find x he2 in
           let (t2,t3) = (projTyp pt2, projTyp pt3) in
           VarMap.add x (Typ (join t2 t3)) acc
    ) he1 VarMap.empty
  in
  let joinLocs he1 he2 =
    if LocMap.is_empty he1 && LocMap.is_empty he2 then he1
    else failwith "TODO joinLocs"
  in
  fun he1 he2 ->
    { HeapEnv.vars = joinVars he1.HeapEnv.vars he2.HeapEnv.vars;
      HeapEnv.locs = joinLocs he1.HeapEnv.locs he2.HeapEnv.locs; }

let genLocVar ?(name="") =
  let i = ref 0 in
  fun () -> incr i; spr "L%s_%d" name !i

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
  ) heapEnv.HeapEnv.vars None

let extendRecdType : recd_type -> recd_type -> recd_type =
fun (TRecd(w1,l1)) (TRecd(w2,l2)) ->
  let width =
    match w1, w2 with
      | ExactDomain, ExactDomain -> ExactDomain
      | _ -> UnknownDomain
  in
  let fields =
    List.fold_left (fun acc (f,t) ->
      if List.mem_assoc f acc
      then (f, t) :: (List.remove_assoc f acc)
      else (f, t) :: acc
    ) l1 l2
  in
  TRecd (width, List.rev fields)

let findInRecdType : field -> recd_type -> typ option =
fun f (TRecd(_,rt)) ->
  if List.mem_assoc f rt then Some (List.assoc f rt) else None

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

  | EBase(VNum _)  -> Ok (exp, (Typ tNum,   heapEnv, MoreOut.empty))
  | EBase(VBool _) -> Ok (exp, (Typ tBool,  heapEnv, MoreOut.empty))
  | EBase(VStr _)  -> Ok (exp, (Typ tStr,   heapEnv, MoreOut.empty))
  | EBase(VUndef)  -> Ok (exp, (Typ tUndef, heapEnv, MoreOut.empty))
  | EBase(VNull)   -> Ok (exp, (Typ tNull,  heapEnv, MoreOut.empty))

  | EVarRead(x) ->
      (match TypeEnv.lookupType x typeEnv with
        | None -> errE (spr "var [%s] isn't defined" x) exp
        | Some(Val(t))
        | Some(InvariantRef(t)) ->
            Ok (exp, (Typ t, heapEnv, MoreOut.addUsedVar x MoreOut.empty))
        | Some(StrongRef) ->
            (match HeapEnv.lookupVar x heapEnv with
              | None -> errE (spr "var [%s] is not in heap env" x) exp
              | Some(pt) ->
                  Ok (exp, (pt, heapEnv, MoreOut.addUsedVar x MoreOut.empty))))

  | EFun(xs,body) when !Settings.castInsertionMode = false ->
      failwith "unannotated functions should not appear in checking mode"

  | EFun(xs,body) ->
      tcBareFun typeEnv heapEnv xs body

  | EAs({exp=EFun(xs,body)},Typ(TArrow(tArgs,tRet))) ->
      tcAnnotatedFun typeEnv heapEnv xs body RelySet.empty tArgs tRet

  | EAs({exp=EFun(xs,body)},OpenArrow(r,tArgs,tRet)) ->
      tcAnnotatedFun typeEnv heapEnv xs body r tArgs tRet

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
      else Ok (exp, (Typ (TArrow ([s], t)), heapEnv, MoreOut.empty))

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

  | EObjRead(e1,e2) ->
      runTcExp2 (typeEnv, heapEnv) (e1, e2)
        (fun (e1,e2) -> Err (eGet e1 e2))
        (fun (e1,e2) (pt1,_,heapEnv,out) ->
           match pt1, isStr e2 with
            | Typ(TRefLoc(l)), Some(f) ->
                (match HeapEnv.lookupLoc l heapEnv with
                  | None -> Err (eGet (eTcErr "not in heap" e1) e2)
                  | Some(rt) ->
                      (match findInRecdType f rt with
                        | None -> Err (eTcErr "field not found" (eGet e1 e2))
                        | Some(tf) -> Ok (eGet e1 e2, (Typ tf, heapEnv, out))))
            | _, None -> Err (eTcErr "dynamic key lookup" (eGet e1 e2))
            | _, _ -> Err (eGet (eTcErr "bad type" e1) e2))

  | EObj _ ->
      failwith "tc EObj: should appear with var declaration"

  | EAs(_,_) ->
      errE "non-function value in ascription" exp

  | ETcErr _ ->
      failwith "tc ETcErr"

and tcBareFun typeEnv heapEnv xs body =

  let typeEnv = TypeEnv.addVar "@ret" (InvariantRef TAny) typeEnv in
  let (typeEnv,heapEnvFun) =
    List.fold_left (fun (acc1,acc2) x ->
      (TypeEnv.addVar x StrongRef acc1, HeapEnv.addVar x (Typ TAny) acc2)
    ) (typeEnv, HeapEnv.empty) xs in

  (* eagerly add all strong assignables to function's input heap env.
     then after type checking the function, synthesize an open arrow
     with all of these variables that were used at least once. *)
  let (rely,heapEnvFun) =
    VarMap.fold (fun x pt (acc1,acc2) ->
      match pt with
        | Typ(t) -> (RelySet.add (x,t) acc1, HeapEnv.addVar x (Typ t) acc2)
        | OpenArrow(_,tArgs,tRet) ->
            let tArrow = TArrow (tArgs, tRet) in
            (RelySet.add (x,tArrow) acc1, HeapEnv.addVar x (Typ tArrow) acc2)
    ) heapEnv.HeapEnv.vars (RelySet.empty, heapEnvFun) in

  run tcStmt (typeEnv, heapEnvFun, body)
    (fun body -> Err (eFun xs body))
    (fun body (ptBody,_,out) ->
       match ptBody with
        | OpenArrow _ ->
            Err (eFun xs (sTcErr "function body has an open type" body))
        | Typ(tBody) ->
            let tArgs = List.map (fun _ -> TAny) xs in
            let tRet = joinTypes (Types.add tBody out.MoreOut.retTypes) in
            let rely =
              RelySet.filter
                (fun (x,_) -> Vars.mem x out.MoreOut.usedVars) rely in
            let arrow = ptArrow rely tArgs tRet in
            let out = { out with MoreOut.retTypes = Types.empty } in
            Ok (eAs (eFun xs body) arrow, (arrow, heapEnv, out)))

and tcAnnotatedFun typeEnv heapEnv xs body rely tArgs tRet =
  if List.length xs <> List.length tArgs
    then failwith "add handling for len(actuals) != len(formals)";
  let typeEnv = TypeEnv.addVar "@ret" (InvariantRef TAny) typeEnv in
  let (typeEnv,heapEnvFun) =
    List.fold_left (fun (acc1,acc2) (x,t) ->
      (TypeEnv.addVar x StrongRef acc1, HeapEnv.addVar x (Typ t) acc2)
    ) (typeEnv, HeapEnv.empty) (List.combine xs tArgs) in
  let typeEnv =
    RelySet.fold
      (fun (x,t) acc -> TypeEnv.addVar x (InvariantRef t) acc) rely typeEnv in
  run tcStmt (typeEnv, heapEnvFun, body)
    (fun body -> Err (eFun xs body))
    (fun body (ptBody,_,_) ->
       match ptBody with
        | OpenArrow _ ->
            Err (eFun xs (sTcErr "function body has an open type" body))
        | Typ(tBody) ->
            let arrow = ptArrow rely tArgs tRet in
            if sub (tBody, tRet) then
              Ok (eAs (eFun xs body) arrow, (arrow, heapEnv, MoreOut.empty))
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
                let out = MoreOut.combine out out' in
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
                     let out = MoreOut.combine out out' in
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
                let tExpected = TypeEnv.lookupRetType typeEnv in
                run coerce (e, t, tExpected)
                   (fun e -> Err (sRet e))
                   (fun e () ->
                      let out = MoreOut.addRetType t out in
                      Ok (sRet e, (Typ TBot, heapEnv, out))))

  | SVarDecl(x,{stmt=SSeq({stmt=SVarAssign(y,{exp=EObj(l)})},s)}) when x = y ->
      if TypeEnv.memVar x typeEnv
      then errS (spr "var [%s] is already scope" x) stmt
      else
        let lx = genLocVar ~name:x () in
        let typeEnv = TypeEnv.addLocationVariable lx typeEnv in
        let typeEnv = TypeEnv.addVar x StrongRef typeEnv in
        let heapEnv = HeapEnv.addVar x (Typ (TRefLoc (LVar lx))) heapEnv in
        let (fieldExps,maybeOutput) =
          List.fold_left (fun (fieldExps,maybeOutput) (field,eField) ->
            match maybeOutput with
             | None -> (fieldExps @ [(field, eField)], None)
             | Some(fieldTypes,heapEnv,out) ->
                 run tcExp (typeEnv, heapEnv, eField)
                   (fun eField -> (fieldExps @ [(field, eField)], None)) 
                   (fun eField (ptField,heapEnv,out') ->
                      match ptField with
                       | OpenArrow _ ->
                           let eField = eTcErr "open type" eField in
                           (fieldExps @ [(field, eField)], None)
                       | Typ(tField) ->
                           let fieldExps = fieldExps @ [(field, eField)] in
                           let fieldTypes = fieldTypes @ [(field, tField)] in
                           let out = MoreOut.combine out out' in
                           (fieldExps, Some (fieldTypes, heapEnv, out)))
          ) ([], Some ([], heapEnv, MoreOut.empty)) l in
        let obj = eObj fieldExps in
        begin match maybeOutput with
          | None -> Err  (sLetRef x (sSeq [sAssign x obj; s]))
          | Some(fieldTypes,heapEnv,out) ->
              let tRecd = TRecd (ExactDomain, fieldTypes) in
              let heapEnv = HeapEnv.addLoc (LVar lx) tRecd heapEnv in
              run tcStmt (typeEnv, heapEnv, s)
                (fun s -> Err (sLetRef x (sSeq [sAssign x obj; s])))
                (fun s (pt,heapEnv,out) ->
                   (* TODO not checking final values *)
                   let heapEnv = HeapEnv.removeVar x heapEnv in
                   let heapEnv = HeapEnv.removeLoc (LVar lx) heapEnv in
                   Ok (sLetRef x (sSeq [sAssign x obj; s]), (pt, heapEnv, out)))
        end

  | SVarDecl(x,s) ->
      if TypeEnv.memVar x typeEnv
      then errS (spr "var [%s] is already scope" x) stmt
      else
        let typeEnv = TypeEnv.addVar x StrongRef typeEnv in
        let heapEnv = HeapEnv.addVar x (Typ (TBase TUndef)) heapEnv in
        run tcStmt (typeEnv, heapEnv, s)
          (fun s -> Err (wrapStmt (SVarDecl (x, s))))
          (fun s (pt,heapEnv,out) ->
             let heapEnv = HeapEnv.removeVar x heapEnv in (* TODO not checking *)
             Ok (sLetRef x s, (pt, heapEnv, out)))

  | SVarAssign(x,e) ->
      begin match TypeEnv.lookupType x typeEnv with
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
                 let heapEnv = HeapEnv.addVar x pt heapEnv in
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
                     let out = MoreOut.combine out1 out2 in
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
                 let out = List.fold_left MoreOut.combine out1 [out2; out3] in
                 Ok (sIf e1 s2 s3, (Typ tJoin, hJoin, out)))))

  | SWhile(e,s) ->
      run tcCoerce (typeEnv, heapEnv, e, tBool)
        (fun e -> Err (sWhile e s))
        (fun e (heapEnv1,out1) ->
           if not (HeapEnv.equal heapEnv heapEnv1)
           then Err (sWhile e (sTcErr "heapEnv1 != heapEnv" s))
           else
             run tcStmt (typeEnv, heapEnv1, s)
               (fun s -> Err (sWhile e s))
               (fun s (_,heapEnv2,out2) ->
                  if not (HeapEnv.equal heapEnv heapEnv2)
                  then Err (sWhile e (sSeq [s; sExp
                              (eTcErr "heapEnv2 != heapEnv" (eStr ""))]))
                  else let out = MoreOut.combine out1 out2 in
                       Ok (sWhile e s, (Typ tUndef, heapEnv, out))))

  | SVarInvariant(x,tGoalX,s) ->
      (match HeapEnv.lookupVar x heapEnv with
        | None -> failwith (spr "varinvariant var [%s] not found" x)
        | Some(OpenArrow _) -> failwith "varinvar open"
        | Some(Typ(tCurrentX)) ->
            if not (sub (tCurrentX, tGoalX)) then
              (* could allow coercion in the bad case instead *)
              let str = spr "varinvariant var [%s]: bad subtyping" x in
              Err (sInvar x tGoalX (sTcErr str s))
            else (* shadow x in type environment *)
              let typeEnv = TypeEnv.addVar x (InvariantRef tGoalX) typeEnv in
              let heapEnv = HeapEnv.removeVar x heapEnv in
              run tcStmt (typeEnv, heapEnv, s)
                (fun s -> Err (sInvar x tGoalX s))
                (fun s stuff -> Ok (sInvar x tGoalX s, stuff)))

  | SClose(xs,s) ->
      let (rely,guarantee) =
        List.fold_left (fun (accR,accG) x ->
          match TypeEnv.lookupType x typeEnv with
           | Some(StrongRef) ->
               (match HeapEnv.lookupVar x heapEnv with
                 | Some(OpenArrow(r,tArgs,tRet)) ->
                     let accR = RelySet.union accR r in
                     let accG = RelySet.add (x, TArrow (tArgs, tRet)) accG in
                     (accR, accG)
                 | Some(Typ _) -> failwith (spr "[%s] is not open func" x)
                 | None -> failwith "sclose 1")
           | _ -> failwith "sclose 2"
        ) (RelySet.empty, RelySet.empty) xs
      in
      if not (RelySet.equal rely guarantee) then
        Err (sClose xs (sTcErr "Rely != Guarantee" s))
      else
        let (typeEnv,heapEnv) =
          RelySet.fold (fun (x,t) (acc1,acc2) ->
            (TypeEnv.addVar x (Val t) acc1, HeapEnv.removeVar x acc2)
          ) rely (typeEnv, heapEnv)
        in
        run tcStmt (typeEnv, heapEnv, s)
          (fun s -> Err (sClose xs s))
          (fun s stuff -> Ok (sClose xs s, stuff))

  | SObjAssign(e1,e2,e3) ->
      runTcExp3 (typeEnv, heapEnv) (e1, e2, e3)
        (fun (e1,e2,e3) -> Err (sSet e1 e2 e3))
        (fun (e1,e2,e3) (pt1,_,pt3,heapEnv,out) ->
           match pt1, isStr e2, pt3 with
            | Typ(TRefLoc(l)), Some(f), Typ(t3) ->
                (match HeapEnv.lookupLoc l heapEnv with
                  | None -> Err (sSet (eTcErr "not in heap" e1) e2 e3)
                  | Some(rt) ->
                      let rt' = TRecd (ExactDomain, [(f,t3)]) in
                      let rt = extendRecdType rt rt' in
                      let heapEnv = HeapEnv.addLoc l rt heapEnv in
                      Ok (sSet e1 e2 e3, (Typ t3, heapEnv, out)))
            | Typ(t1), _, _ ->
                Err (sSet (eTcErr (spr "not a strong object: %s"
                  (Printer.strTyp t1)) e1) e2 e3)
            | _, None, _ ->
                Err (sSet e1 (eTcErr "dynamic key" e2) e3)
            | _, _, OpenArrow _ ->
                Err (sSet e1 e2 (eTcErr "open function type" e3)))

  | SLoadedSrc(f,s) ->
      run tcStmt (typeEnv, heapEnv, s)
        (fun s -> Err (wrapStmt (SLoadedSrc (f, s))))
        (fun s stuff -> Ok (wrapStmt (SLoadedSrc (f, s)), stuff))

  | SExternVal(x,tx,s) ->
      let typeEnv = TypeEnv.addVar x (Val tx) typeEnv in
      run tcStmt (typeEnv, heapEnv, s)
        (fun s -> Err (wrapStmt (SExternVal (x, tx, s))))
        (fun s stuff -> Ok (wrapStmt (SExternVal (x, tx, s)), stuff))

and runTcExp2 (typeEnv, heapEnv) (e1, e2) fError fOk =
  run tcExp (typeEnv, heapEnv, e1)
    (fun e1 -> fError (e1, e2))
    (fun e1 (pt1,heapEnv,out1) -> run tcExp (typeEnv, heapEnv, e2)
       (fun e2 -> fError (e1, e2))
       (fun e2 (pt2,heapEnv,out2) ->
          let out = MoreOut.combine out1 out2 in
          fOk (e1, e2) (pt1, pt2, heapEnv, out)))

and runTcExp3 (typeEnv, heapEnv) (e1, e2, e3) fError fOk =
  run tcExp (typeEnv, heapEnv, e1)
    (fun e1 -> fError (e1, e2, e3))
    (fun e1 (pt1,heapEnv,out1) -> run tcExp (typeEnv, heapEnv, e2)
       (fun e2 -> fError (e1, e2, e3))
       (fun e2 (pt2,heapEnv,out2) -> run tcExp (typeEnv, heapEnv, e3)
          (fun e3 -> fError (e1, e2, e3))
          (fun e3 (pt3,heapEnv,out3) ->
             let out = List.fold_left MoreOut.combine out1 [out2; out3] in
             fOk (e1, e2, e3) (pt1, pt2, pt3, heapEnv, out))))

(* TODO a general tcExpN version for app1, app2, and eobj *)

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
  match tcStmt (TypeEnv.empty, HeapEnv.empty, prog) with
   | Ok(prog,(_,_,_)) -> Ok (prog, ())
   | Err(prog)        -> Err prog
