
open Lang
open LangUtils
open Printer

module StrMap = Utils.StrMap

type type_env_binding =
  | Val of typ
  | StrongRef
  | InvariantRef of typ

module TypeEnv = struct

  type t = { bindings: type_env_binding VarMap.t;
             loc_vars: Vars.t;
             ty_abbrevs: (ty_var list * mu_type) StrMap.t; }

  let empty : t =
    { bindings = VarMap.empty;
      loc_vars = Vars.empty;
      ty_abbrevs = StrMap.empty; }

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

  let addLocVar : var -> t -> t =
  fun x typeEnv ->
    { typeEnv with loc_vars = Vars.add x typeEnv.loc_vars }

  let addLocVars : var list -> t -> t =
  fun ls typeEnv ->
    List.fold_left (fun acc l -> addLocVar l acc) typeEnv ls

  let addTyAbbrev : ty_abbrev -> (ty_var list * mu_type) -> t -> t =
  fun x def typeEnv ->
    { typeEnv with ty_abbrevs = StrMap.add x def typeEnv.ty_abbrevs }

  let lookupTyAbbrev : ty_abbrev -> t -> (ty_var list * mu_type) option =
  fun x typeEnv ->
    if StrMap.mem x typeEnv.ty_abbrevs
    then Some (StrMap.find x typeEnv.ty_abbrevs)
    else None

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
  | Typ(t) -> t
  | _ -> failwith "projTyp"

let rec sub = function
  | s, t when s = t -> true
  | TBot, _ -> true
  | _, TAny -> true
  | s, TUnion ts when List.mem s ts -> true
  (* TODO *)
  | _ -> false

and recdSub (TRecd(width1,fts1), TRecd(width2,fts2)) =
  let widthOkay =
    match width1, width2 with
      | UnknownDomain, ExactDomain -> false
      | _, UnknownDomain ->
          List.for_all (fun (f,_) -> List.mem_assoc f fts1) fts2
      | ExactDomain, ExactDomain ->
          List.for_all (fun (f,_) -> List.mem_assoc f fts1) fts2
          && List.for_all (fun (f,_) -> List.mem_assoc f fts2) fts1
  in
  if widthOkay
  then List.for_all (fun (f,t2) -> sub (List.assoc f fts1, t2)) fts2
  else false

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

let rec stripExists : pre_type -> (var list * pre_type) =
function
  | Exists(l,pt) -> let (ls,pt0) = stripExists pt in (l::ls, pt0)
  | pt           -> ([], pt)

let rec addExists : var list -> pre_type -> pre_type =
fun locs pt ->
  match locs with
    | []    -> pt
    | l::ls -> Exists (l, addExists ls pt)

let rec stripClosedType : pre_type -> (var list * typ) option =
function
  | OpenArrow _  -> None
  | Typ(t)       -> Some ([], t)
  | Exists(l,pt) ->
      (match stripClosedType pt with
         | Some(ls,t) -> Some (l::ls, t)
         | None       -> None)

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

let genLocVar =
  let i = ref 0 in
  (fun ?(name="") () -> incr i; spr "L%s_%d" name !i)

let isLambda exp = match exp.exp with
  | EFun _ | EAs({exp=EFun _},_) -> true
  | _ -> false

let maybeAddSomeVarInvariants heapEnv stmt =
  VarMap.fold (fun x pt acc ->
    match pt, acc with
      | Typ(TBase(TUndef)), _
      | OpenArrow _, _  -> acc
      | Typ(t), None    -> Some (sTcInsert (sInvar x t stmt))
      | Typ(t), Some(s) -> Some (sTcInsert (sInvar x t s))
      | Exists _, _     -> failwith "maybeAddSomeVarInvariants"
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

type recd_get_field =
  | Bound of typ
  | NotBound
  | MaybeBound

let findInRecdType : field -> recd_type -> recd_get_field =
fun f (TRecd(width,rt)) ->
  if List.mem_assoc f rt then       Bound (List.assoc f rt)
  else if width = ExactDomain then  NotBound
  else                              MaybeBound

let removeLocsFromType : typ -> typ =
fun t ->
  mapTyp (function TRefLoc _ -> TAny | s -> s) t

let unrollProperMu : mu_type -> (var * recd_type) -> recd_type =
fun mu -> function
  | "_", rt -> rt
  | x, TRecd(width,fts) ->
      let foo = mapTyp (function TVar(y) when x = y -> TRefMu mu | t -> t) in
      let fts = List.map (fun (f, t) -> (f, foo t)) fts in
      TRecd (width, fts)

let unrollMu : TypeEnv.t -> mu_type -> recd_type =
fun typeEnv mu ->
  match mu with
    | Mu(x,rt) -> unrollProperMu mu (x,rt)
    | MuAbbrev(t,[]) ->
        (match TypeEnv.lookupTyAbbrev t typeEnv with
          | Some([],Mu(x,rt)) -> unrollProperMu mu (x,rt)
          | None -> failwith "unrollMu 1"
          | _ -> failwith "unrollMu 2")
    | MuAbbrev _ -> failwith "unrollMu with type args"

let castToMu : typ -> mu_type option =
fun t ->
  let default = Mu ("_", TRecd (UnknownDomain, [])) in
  match t with
    | TMaybe(TRefMu(mu)) -> Some mu
    | TUnion(ts) ->
        let mus =
          List.fold_left
            (fun acc -> function TRefMu(mu) -> mu :: acc | _ -> acc) [] ts in
        (match mus with
           | [mu] -> Some mu
           | []   -> Some default
           | _    -> None) (* don't want unions with multiple object types *)
    | _ ->
        Some default

let transitiveAssumeVars f heapEnv =
  let rec doOne f acc =
    let acc = Vars.add f acc in
    match HeapEnv.lookupVar f heapEnv with
      | Some(OpenArrow(rely,_,_)) ->
          RelySet.fold
            (fun (g,_) acc -> if Vars.mem g acc then acc else doOne g acc)
            rely acc
      | _ -> acc
  in
  let vars = doOne f Vars.empty in
  Vars.elements vars

let sHole = sExp (eVar "REMOVE_ME")

type lvalue =
  | LvalVar of var
  | LvalPath of var * field list

let rec lvalOf exp = match exp.exp with
  | EVarRead(x) -> Some (LvalVar x)
  | EObjRead(e1,{exp=EBase(VStr(f))}) ->
      (match lvalOf e1 with
        | Some(LvalVar(x))     -> Some (LvalPath (x, [f]))
        | Some(LvalPath(x,fs)) -> Some (LvalPath (x, fs @ [f]))
        | None                 -> None)
  | _ -> None

let rec eLval = function
  | LvalVar(x) -> eVar x
  | LvalPath(x,[]) -> eVar x
  | LvalPath(x,fs) ->
      let fs = List.rev fs in
      let (hd,tl) = (List.hd fs, List.tl fs) in
      eGet (eLval (LvalPath (x, List.rev tl))) (eStr hd)

let sAssignLval lv e =
  match lv with
    | LvalVar(x) -> sAssign x e
    | LvalPath(_,[]) -> failwith "sAssignLval"
    | LvalPath(x,fs) ->
        let fs = List.rev fs in
        let (hd,tl) = (List.hd fs, List.tl fs) in
        sSet (eLval (LvalPath (x, List.rev tl))) (eStr hd) e

type ('a, 'b) result =
  | Ok of 'a * 'b
  | Err of 'a

let run foo args fError fOk =
  match foo args with
    | Err(a)  -> fError a
    | Ok(a,b) -> fOk a b

let runHandleError foo args fError =
  run foo args fError (fun a b -> Ok (a, b))

let errE s e       = Err (eTcErr s e)
let sTcErr s stmt  = sSeq [sExp (eTcErr s (eStr "")); stmt]
let errS s stmt    = Err (sTcErr s stmt)

(* TODO *)
let compatible s t = match s, t with
  | TRefLoc(l1), TRefLoc(l2) -> l1 = l2
  | _, TRefLoc _ | TRefLoc _, _ -> false
  | _ -> true

let coerce (e, s, t) =
  let (s1,s2) = (strTyp s, strTyp t) in
  if sub (s, t) then
    Ok (e, false)
  else if not !Settings.castInsertionMode then
    Err (eTcErr (spr "not a subtype:\n%s\n%s" s1 s2) e)
  else if compatible s t then
    Ok (eApp (eTcInsert (eCast s t)) [e], true)
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

  | EApp({exp=ECast((TRefMu(mu) as s),((TRefMu(mu')) as t))},[e]) ->
      (* TODO *)
      (match mu, mu' with
        | Mu("_",rt), Mu("_",rt') ->
            run tcExp (typeEnv, heapEnv, e)
              (fun e -> Err (eApp (eCast s t) [e]))
              (fun e (pt,heapEnv,out) ->
                 match pt with
                  | Typ(TRefLoc(l)) ->
                      let cast = eApp (eCast s t) [e] in
                      (match HeapEnv.lookupLoc l heapEnv with
                        | Some(rt0) when rt = rt0 ->
                            let heapEnv = HeapEnv.addLoc l rt' heapEnv in
                            Ok (cast, (Typ tUndef, heapEnv, out))
                        | _ ->
                            Err (eTcErr "app-cast error" cast))
                  | _ ->
                      Err (eTcErr "app-cast error" (eApp (eCast s t) [e])))
        | Mu _, Mu _ ->
            failwith "TODO cast between mu types"
        | _ ->
            failwith "TODO cast involving abbrevs")

  | ECast(s,t) ->
      Ok (exp, (Typ (TArrow ([s], t)), heapEnv, MoreOut.empty))

  | EApp(eFun,eArgs) ->
      run tcExp (typeEnv, heapEnv, eFun)
        (fun eFun -> Err (eApp eFun eArgs))
        (fun eFun (ptFun,heapEnv,outFun) ->
           match ptFun with
            | Exists _ ->
                Err (eApp (eTcErr "function has existential type" eFun) eArgs)
            | OpenArrow _ ->
                let err = "function has open type" in
                (match lvalOf eFun with
                  | Some(LvalVar(f)) ->
                      (* look for the dummy stmt sHole when backtracking *)
                      let fs = transitiveAssumeVars f heapEnv in
                      let sRetry = sClose fs sHole in
                      Err (eApp (eTcErrRetry err eFun sRetry) eArgs)
                  | _ -> 
                      Err (eApp (eTcErr err eFun) eArgs))
            | Typ(TArrow(tArgs,tRet)) ->
                tcApp1 typeEnv heapEnv outFun eFun eArgs tArgs tRet
            | Typ(tFun) ->
                tcApp2 typeEnv heapEnv outFun eFun eArgs tFun)

  | EObj(fes) ->
      tcObjLit typeEnv heapEnv (genLocVar ()) fes

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
                        | Bound(tf) ->
                            Ok (eGet e1 e2, (Typ tf, heapEnv, out))
                        | NotBound ->
                            if !Settings.strictObjGet
                            then Err (eTcErr "field not found" (eGet e1 e2))
                            else Ok (eGet e1 e2, (Typ tUndef, heapEnv, out))
                        | MaybeBound ->
                            if !Settings.strictObjGet
                            then Err (eTcErr "field not found" (eGet e1 e2))
                            else Ok (eGet e1 e2, (Typ TAny, heapEnv, out))))
            | Typ(TRefMu(mu)), Some(f) ->
                let err = "trying to read from mu type" in
                (match lvalOf e1 with
                  | Some(lv) ->
                      let sRetry = sAssignLval lv (eUnfold mu (eLval lv)) in
                      Err (eGet (eTcErrRetry err e1 sRetry) e2)
                  | _ ->
                      Err (eGet (eTcErr err e1) e2))
            | Typ(t), _ ->
                let err = spr "object type isn't strong:\n %s" (strTyp t) in
                (match lvalOf e1, castToMu t with
                  | Some(lv), Some(mu) ->
                      let cast = eCast t (TRefMu mu) in
                      let sRetry = sAssignLval lv (eApp cast [eLval lv]) in
                      Err (eGet (eTcErrRetry err e1 sRetry) e2)
                  | _, _ ->
                      Err (eGet (eTcErr err e1) e2))
            | _, None ->
                Err (eTcErr "dynamic key lookup" (eGet e1 e2))
            | _, _ ->
                let err = spr "object type not strong:\n %s" (strPreTyp pt1) in
                Err (eGet (eTcErr err e1) e2))

  | EFold(mu,e) ->
      run tcExp (typeEnv, heapEnv, e)
        (fun e -> Err (eFold mu e))
        (fun e (pt,heapEnv,out) ->
           let (locs,pt) = stripExists pt in
           match pt with
            | Typ(TRefLoc(l)) ->
                (match HeapEnv.lookupLoc l heapEnv with
                  | None -> Err (eFold mu (eTcErr "not in heap" e))
                  | Some(rt') ->
                      let rt = unrollMu typeEnv mu in
                      if recdSub (rt', rt) then
                        let heapEnv = HeapEnv.removeLoc l heapEnv in
                        let tPtr = addExists locs (Typ (TRefMu mu)) in
                        Ok (eFold mu e, (tPtr, heapEnv, out))
                      else
                        let (s1,s2) = (strRecdTyp rt', strRecdTyp rt) in
                        let sErr = spr "bad recd subtyping\n %s\n %s\n" s1 s2 in
                        Err (eFold mu (eTcErr sErr e)))
            | _ ->
                let err = spr "object isn't strong:\n%s\n" (strPreTyp pt) in
                Err (eFold mu (eTcErr err e)))

  | EUnfold(mu,e) ->
      run tcExp (typeEnv, heapEnv, e)
        (fun e -> Err (eUnfold mu e))
        (fun e (pt,heapEnv,out) ->
           match pt with
            | Typ(TRefMu(mu')) when mu <> mu' ->
                Err (eTcErr "mu annotation doesn't match" (eUnfold mu e))
            | Typ(TRefMu _ ) ->
                let locObj = genLocVar () in
                let rt = unrollMu typeEnv mu in
                let heapEnv = HeapEnv.addLoc (LVar locObj) rt heapEnv in
                let ptr = Typ (TRefLoc (LVar locObj)) in
                Ok (eUnfold mu e, (Exists (locObj, ptr), heapEnv, out))
            | _ ->
                Err (eUnfold mu (eTcErr "object isn't mu type" e)))

  | ETcInsert(e) ->
      run tcExp (typeEnv, heapEnv, e)
        (fun e -> Err (eTcInsert e))
        (fun e stuff -> Ok (eTcInsert e, stuff))

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
        | Exists _ -> failwith "tcBareFun exists"
        | Typ(t) -> (RelySet.add (x,t) acc1, HeapEnv.addVar x (Typ t) acc2)
        | OpenArrow(_,tArgs,tRet) ->
            let tArrow = TArrow (tArgs, tRet) in
            (RelySet.add (x,tArrow) acc1, HeapEnv.addVar x (Typ tArrow) acc2)
    ) heapEnv.HeapEnv.vars (RelySet.empty, heapEnvFun) in

  run tcStmt (typeEnv, heapEnvFun, body)
    (fun body -> Err (eFun xs body))
    (fun body (ptBody,_,out) ->
       (* don't need locs, because no effects in function types (for now) *)
       let (_,ptBody) = stripExists ptBody in
       match ptBody with
        | Exists _ -> assert false
        | OpenArrow _ ->
            Err (eFun xs (sTcErr "function body has an open type" body))
        | Typ(tBody) ->
            let tArgs = List.map (fun _ -> TAny) xs in
            let tRet = joinTypes (Types.add tBody out.MoreOut.retTypes) in
            let rely =
              RelySet.filter
                (fun (x,_) -> Vars.mem x out.MoreOut.usedVars) rely in
            let tRet = removeLocsFromType tRet in
            let arrow = ptArrow rely tArgs tRet in
            let out = { out with MoreOut.retTypes = Types.empty } in
            Ok (eAs (eFun xs body) arrow, (arrow, heapEnv, out)))

and tcAnnotatedFun typeEnv heapEnv xs body rely tArgs tRet =
  let origArrow = OpenArrow (rely, tArgs, tRet) in
  if List.length xs <> List.length tArgs
    then failwith "add handling for len(actuals) != len(formals)";
  let typeEnv = TypeEnv.addVar "@ret" (InvariantRef tRet) typeEnv in
  let (typeEnv,heapEnvFun) =
    List.fold_left (fun (acc1,acc2) (x,t) ->
      (TypeEnv.addVar x StrongRef acc1, HeapEnv.addVar x (Typ t) acc2)
    ) (typeEnv, HeapEnv.empty) (List.combine xs tArgs) in
  let typeEnv =
    RelySet.fold
      (fun (x,t) acc -> TypeEnv.addVar x (InvariantRef t) acc) rely typeEnv
  in
  run tcStmt (typeEnv, heapEnvFun, body)
    (fun body -> Err (eAs (eFun xs body) origArrow))
    (fun body (ptBody,_,_) ->
       let (_,ptBody) = stripExists ptBody in (* same as above *)
       match ptBody with
        | Exists _ -> assert false
        | OpenArrow _ ->
            let err = "function body has an open type" in
            Err (eAs (eFun xs (sTcErr err body)) origArrow)
        | Typ(tBody) ->
            let arrow = ptArrow rely tArgs tRet in
            if sub (tBody, tRet) then
              Ok (eAs (eFun xs body) arrow, (arrow, heapEnv, MoreOut.empty))
            else
              let err = "fun has bad fall-thru type" in
              Err (eAs (eFun xs (sTcErr err body)) origArrow))

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
    (fun eFun _ ->
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

and tcObjLit typeEnv heapEnv locObj fieldExps =
  let (fieldExps,maybeOutput) =
    List.fold_left (fun (fieldExps,maybeOutput) (field,eField) ->
      match maybeOutput with
       | None -> (fieldExps @ [(field, eField)], None)
       | Some(existentials,fieldTypes,heapEnv,out) ->
           run tcExp (typeEnv, heapEnv, eField)
             (fun eField -> (fieldExps @ [(field, eField)], None)) 
             (fun eField (ptField,heapEnv,out') ->
                match stripClosedType ptField with
                 | None ->
                     let eField = eTcErr "bad pre-type" eField in
                     (fieldExps @ [(field, eField)], None)
                 | Some(locs,tField) ->
                     let fieldExps = fieldExps @ [(field, eField)] in
                     let fieldTypes = fieldTypes @ [(field, tField)] in
                     let out = MoreOut.combine out out' in
                     let existentials = existentials @ locs in
                     (fieldExps, Some (existentials, fieldTypes, heapEnv, out)))
    ) ([], Some ([], [], heapEnv, MoreOut.empty)) fieldExps in
  let obj = eObj fieldExps in
  begin match maybeOutput with
    | None -> Err obj
    | Some(existentials,fieldTypes,heapEnv,out) ->
        let tRecd = TRecd (ExactDomain, fieldTypes) in
        let tPtr = Typ (TRefLoc (LVar locObj)) in
        let ptPtr = addExists (existentials @ [locObj]) tPtr in
        let heapEnv = HeapEnv.addLoc (LVar locObj) tRecd heapEnv in
        Ok (obj, (ptPtr, heapEnv, out))
  end

and tcStmt ((typeEnv, heapEnv, stmt) as args) = match stmt.stmt with

  | SReturn(e) | SVarAssign(_,e)
    when isLambda e && !Settings.castInsertionMode = true ->
      begin match maybeAddSomeVarInvariants heapEnv stmt with
        | Some(stmt) -> tcStmt (typeEnv, heapEnv, stmt)
        | None       -> _tcStmt args
      end

  | _ -> _tcStmt args

and _tcStmt (typeEnv, heapEnv, stmt) =

  if not !Settings.castInsertionMode then __tcStmt (typeEnv, heapEnv,stmt)
  else (* try some backtracking upon failure *)

  runHandleError __tcStmt (typeEnv, heapEnv, stmt)
    begin fun stmtErr ->
      let retryStmts =
        foldStmt
          (fun acc -> function ETcErr(_,_,Some(s)) -> s::acc | _ -> acc)
          (fun acc s -> acc) [] stmtErr
      in
      List.fold_left (fun result sRetry ->
        match result, sRetry with
          | Ok _, _ ->
              result
          | Err _, {stmt=SClose(xs,s0)} when s0 = sHole ->
              tcStmt (typeEnv, heapEnv, sTcInsert (sClose xs stmt))
          | Err _, _ ->
              tcStmt (typeEnv, heapEnv, sSeq [sTcInsert sRetry; stmt])
      ) (Err stmtErr) retryStmts
    end

and __tcStmt (typeEnv, heapEnv, stmt) = match stmt.stmt with

  | SExp(e) ->
      run tcExp (typeEnv, heapEnv, e)
        (fun e -> Err (sExp e))
        (fun e (pt,heapEnv,out) -> Ok (sExp e, (pt, heapEnv, out)))

  | SReturn(e) ->
      let eOrig = e in
      run tcExp (typeEnv, heapEnv, e)
        (fun e -> Err (sRet e))
        (fun e (pt,heapEnv,out) ->
           let (locs,pt) = stripExists pt in
           match pt with
            | Exists _ -> assert false
            | OpenArrow _ -> Err (sTcErr "return exp has open type" (sRet e))
            | Typ(t) ->
                let tExpected = TypeEnv.lookupRetType typeEnv in
                run coerce (e, t, tExpected)
                  (fun eErr ->
                     match lvalOf eOrig, t, tExpected with
                      | Some(lv), TRefLoc _, TRefMu(mu) ->                   
                          let sRetry = sAssignLval lv (eFold mu (eLval lv)) in
                          Err (sRet (eTcErrRetry "bad ret type" e sRetry))
                      | _, TRefLoc _, TRefMu(mu) ->
                          (* backtracking *)
                          run tcExp (typeEnv, heapEnv, eFold mu eOrig)
                            (fun _ -> Err (sRet eErr))
                            (fun e stuff ->
                               Ok (sRet (eTcInsert (eFold mu eOrig)), stuff))
                      | _ -> Err (sRet e))
                  (fun e _ ->
                     let out = MoreOut.addRetType t out in
                     Ok (sRet e, (addExists locs (Typ TBot), heapEnv, out))))

    (* combination of SVarDecl, SVarAssign, EObj, and SSeq rules in order
       to allocate the object at Lx_%d *)
  | SVarDecl(x,{stmt=SSeq({stmt=SVarAssign(y,{exp=EObj(l)})},s)}) when x = y ->
      if TypeEnv.memVar x typeEnv
      then errS (spr "var [%s] is already scope" x) stmt
      else begin
        let locObj = genLocVar ~name:x () in
        match tcObjLit typeEnv heapEnv locObj l with
         | Err(obj) -> Err (sLetRef x (sSeq [sAssign x obj; s]))
         | Ok(obj,(ptObj,heapEnv,out)) ->
             let (locs,ptObj) = stripExists ptObj in
             let typeEnv = TypeEnv.addLocVars locs typeEnv in
             let typeEnv = TypeEnv.addLocVar locObj typeEnv in
             let typeEnv = TypeEnv.addVar x StrongRef typeEnv in
             let heapEnv = HeapEnv.addVar x ptObj heapEnv in
             run tcStmt (typeEnv, heapEnv, s)
               (fun s -> Err (sLetRef x (sSeq [sAssign x obj; s])))
               (fun s (pt,heapEnv,out) ->
                  let heapEnv = HeapEnv.removeVar x heapEnv in
                  let pt = addExists (locs @ [locObj]) pt in
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
             let heapEnv = HeapEnv.removeVar x heapEnv in
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
                 let (locs,pt) = stripExists pt in
                 let heapEnv = HeapEnv.addVar x pt heapEnv in
                 Ok (sAssign x e, (addExists locs pt, heapEnv, out)))
      end

  | SSeq(s1,s2) ->
      run tcStmt (typeEnv, heapEnv, s1)
        (fun s1 -> Err (sSeq [s1; s2]))
        (fun s1 (pt1,heapEnv1,out1) ->
           let (locs1,pt1') = stripExists pt1 in
           match pt1' with
            | Typ(TBot) -> Ok (sSeq [s1; s2], (pt1, heapEnv1, out1))
            | _ ->
                let typeEnv = TypeEnv.addLocVars locs1 typeEnv in
                run tcStmt (typeEnv, heapEnv1, s2)
                  (fun s2 -> Err (sSeq [s1; s2]))
                  (fun s2 (pt2,heapEnv2,out2) ->
                     let out = MoreOut.combine out1 out2 in
                     Ok (sSeq [s1; s2], (addExists locs1 pt2, heapEnv2, out))))

  | SIf(e1,s2,s3) ->
      (* requiring boolean guard for now *)
      run tcCoerce (typeEnv, heapEnv, e1, tBool)
        (fun e1 -> Err (sIf e1 s2 s3))
        (fun e1 (heapEnv,out1) -> run tcStmt (typeEnv, heapEnv, s2)
           (fun s2 -> Err (sIf e1 s2 s3))
           (fun s2 (ptThen,heapEnv2,out2) -> run tcStmt (typeEnv, heapEnv, s3)
              (fun s3 -> Err (sIf e1 s2 s3))
              (fun s3 (ptElse,heapEnv3,out3) ->
                 let ptThen = snd (stripExists ptThen) in
                 let ptElse = snd (stripExists ptElse) in
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
                  if not (HeapEnv.equal heapEnv heapEnv2) then
                    let err = "heapEnv2 != heapEnv" in
                    Err (sWhile e (sSeq [s; sExp (eTcErr err (eStr ""))]))
                  else
                    let out = MoreOut.combine out1 out2 in
                    Ok (sWhile e s, (Typ tUndef, heapEnv, out))))

  | SVarInvariant(x,tGoalX,s) ->
      (match HeapEnv.lookupVar x heapEnv with
        | None -> failwith (spr "varinvariant var [%s] not found" x)
        | Some(OpenArrow _) -> failwith "varinvar open"
        | Some(Exists _) -> failwith "varinvar exists"
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
      if xs = [] then Err (sTcErr "need at least one var" (sClose xs s)) else
      let (rely,guarantee) =
        List.fold_left (fun (accR,accG) x ->
          match TypeEnv.lookupType x typeEnv with
           | Some(StrongRef) ->
               (match HeapEnv.lookupVar x heapEnv with
                 | Some(OpenArrow(r,tArgs,tRet)) ->
                     let accR = RelySet.union accR r in
                     let accG = RelySet.add (x, TArrow (tArgs, tRet)) accG in
                     (accR, accG)
                 | Some(Typ _)
                 | Some(Exists _) -> failwith (spr "[%s] is not open func" x)
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
           let (locs3,pt3) = stripExists pt3 in
           match pt1, isStr e2, pt3 with
            | Typ(TRefLoc(l)), Some(f), Typ(t3) ->
                (match HeapEnv.lookupLoc l heapEnv with
                  | None -> Err (sSet (eTcErr "not in heap" e1) e2 e3)
                  | Some(rt) ->
                      let rt' = TRecd (ExactDomain, [(f,t3)]) in
                      let rt = extendRecdType rt rt' in
                      let heapEnv = HeapEnv.addLoc l rt heapEnv in
                      Ok (sSet e1 e2 e3, (addExists locs3 (Typ t3), heapEnv, out)))
            | _, None, _ ->
                Err (sSet e1 (eTcErr "dynamic key" e2) e3)
            | _, _, OpenArrow _ ->
                Err (sSet e1 e2 (eTcErr "open function type" e3))
            | Typ _, _, _
            | Exists _, _, _
            | OpenArrow _, _, _ ->
                Err (sSet (eTcErr "not strong object type" e1) e2 e3))

  | SLoadedSrc(f,s) ->
      run tcStmt (typeEnv, heapEnv, s)
        (fun s -> Err (wrapStmt (SLoadedSrc (f, s))))
        (fun s stuff -> Ok (wrapStmt (SLoadedSrc (f, s)), stuff))

  | SExternVal(x,tx,s) ->
      let typeEnv = TypeEnv.addVar x (Val tx) typeEnv in
      run tcStmt (typeEnv, heapEnv, s)
        (fun s -> Err (wrapStmt (SExternVal (x, tx, s))))
        (fun s stuff -> Ok (wrapStmt (SExternVal (x, tx, s)), stuff))

  | STcInsert(s) ->
      run tcStmt (typeEnv, heapEnv, s)
        (fun s -> Err (sTcInsert s))
        (fun s stuff -> Ok (sTcInsert s, stuff))

  | STyAbbrev(x,def,s) ->
      (* TODO check well-formedness of def *)
      let typeEnv = TypeEnv.addTyAbbrev x def typeEnv in
      run tcStmt (typeEnv, heapEnv, s)
        (fun s -> Err (sTyDef x def s))
        (fun s stuff -> Ok (sTyDef x def s, stuff))

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
  let eInit = e in
  run tcExp (typeEnv, heapEnv, e)
    (fun e -> Err e)
    (fun e (pt,heapEnv,out) ->
       match pt with
        | Exists _ -> errE "need to bind existentials?" e
        | OpenArrow _ -> errE "cannot coerce from open arrow" e
        | Typ(t) ->
            run coerce (e, t, tGoal)
              (fun e -> Err e)
              (fun e insertedCast ->
                 if not insertedCast then Ok (e, (heapEnv, out))
                 (* coercion succeeded, but hoist it out to an assignment *)
                 (* if possible rather than inserting the cast locally    *)
                 else begin
                   match lvalOf eInit with
                    | None -> Ok (e, (heapEnv, out))
                    | Some(lv) ->
                        let sRetry = sAssignLval lv e in
                        Err (eTcErrRetry "tcCoerce backtracking" eInit sRetry)
                 end))

let removeTcInserts prog =
  mapStmt (* keep in sync with what tc can insert *)
    (function
      | EApp({exp=ETcInsert{exp=ECast _}},[eArg]) -> eArg.exp
      | ETcInsert({exp=EFold(_,e)}) -> e.exp
      | e -> e)
    (function
      | STcInsert({stmt=SClose(_,s)})
      | STcInsert({stmt=SVarInvariant(_,_,s)})
      | STcInsert({stmt=SSeq({stmt=SVarAssign _},s)})
      | STcInsert({stmt=SSeq({stmt=SObjAssign _},s)}) -> s.stmt
      | s -> s)
    prog

let typecheck prog =
  let prog =
    if !Settings.castInsertionMode
    then removeTcInserts prog (* remove [...] expressions and statements *)
    else prog
  in
  match tcStmt (TypeEnv.empty, HeapEnv.empty, prog) with
   | Ok(prog,_) -> Ok (prog, ())
   | Err(prog)  -> Err prog

