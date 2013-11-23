
open Lang
open LangUtils
open Printer

module StrMap = Utils.StrMap

let ifSome opt f = match opt with Some(x) -> f x | _ -> opt

let ifNone opt f = match opt with None -> f () | _ -> opt

type type_env_binding =
  | Val of typ
  | StrongRef
  | InvariantRef of typ

module TypeEnv = struct

  type t = { bindings: type_env_binding VarMap.t;
             loc_vars: Vars.t;
             ty_abbrevs: (ty_var list * mu_type) StrMap.t;
             ret_world: output_world; }

  let empty : t =
    { bindings = VarMap.empty;
      loc_vars = Vars.empty;
      ty_abbrevs = StrMap.empty;
      ret_world = ([], TBot, []); }

  let lookupType : var -> t -> type_env_binding option =
  fun x typeEnv ->
    if VarMap.mem x typeEnv.bindings
    then Some (VarMap.find x typeEnv.bindings)
    else None

  let addRetWorld : output_world -> t -> t =
  fun w typeEnv ->
    { typeEnv with ret_world = w }

  let lookupRetWorld : t -> output_world =
  fun typeEnv ->
    typeEnv.ret_world

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

  type t = { vars: pre_type VarMap.t; locs: loc_binding LocMap.t; }

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

  let addLoc : loc -> loc_binding -> t -> t =
  fun l lb he ->
    { he with locs = LocMap.add l lb he.locs }

  let lookupLoc : loc -> t -> loc_binding option =
  fun l heapEnv ->
    if LocMap.mem l heapEnv.locs
    then Some (LocMap.find l heapEnv.locs)
    else None

  let removeLoc : loc -> t -> t =
  fun l he ->
    { he with locs = LocMap.remove l he.locs }

  let memLoc : loc -> t -> bool =
  fun l heapEnv ->
    LocMap.mem l heapEnv.locs

  let equal : t -> t -> bool =
  fun he1 he2 ->
    let cmp x y = compare x y = 0 in
    VarMap.equal cmp he1.vars he2.vars && LocMap.equal cmp he1.locs he2.locs

  let strLocs : t -> string =
  fun he ->
    let l =
      LocMap.fold (fun l lb acc -> strHeapBinding (l,lb) :: acc) he.locs [] in
    spr "(%s)" (commas (List.rev l))

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

let (genLocVar,clearLocVarCounter) =
  let i = ref 0 in
  (fun ?(name="") () -> incr i; spr "L%s_%d" name !i),
  (fun () -> i := 0)

let (genSym,clearTmpCounter) =
  let i = ref 0 in
  (fun ?(name="") () -> incr i; spr "__%s%d" name !i),
  (fun () -> i := 0)

let projTyp = function
  | Typ(t) -> t
  | _ -> failwith "projTyp"

let wellFormed : TypeEnv.t -> pre_type -> bool =
fun typeEnv pt ->
  (* TODO *)
  true

let rec sub_ :
     (unit -> 'a)    (* success handler for everything but TExistsRef *)
  -> (unit -> 'a)    (* failure handler *)
  -> (loc * loc_var * mu_type -> 'a) option (* handler for TExistsRef *)
  -> typ -> typ -> 'a =
fun ok bad handlerExistsRef s t ->
  let recurse = sub_ ok bad handlerExistsRef in
  match s, t with
    | s, t when s = t -> ok () 
    | TBot, _ -> ok ()
    | _, TAny -> ok ()
    | s, TUnion ts when List.mem s ts -> ok ()
    | TBase TNull, TMaybe _
    | TBase TUndef, TMaybe _ -> ok ()
    | TRefLoc l, TMaybe TExistsRef (lvar, mu) ->
        recurse (TRefLoc l) (TExistsRef (lvar, mu))
    | TMaybe s, TMaybe t -> recurse s t
    | s, TMaybe t -> recurse s t
    | TRefLoc l, TExistsRef (lvar, mu) ->
        (match handlerExistsRef with
          | Some f -> f (l, lvar, mu)
          | None -> failwith "sub_: TExistsRef shouldn't be here")
    | _ -> bad ()   

let sub : typ -> typ -> bool =
fun s t ->
  sub_ (fun () -> true) (fun () -> false) None s t

let subAndPack : HeapEnv.t -> typ -> typ -> HeapEnv.t option =
fun heapEnv ->
  sub_ (fun () -> Some heapEnv)
       (fun () -> None)
       (Some (fun (locWitness, locExists, muExists) ->
                match HeapEnv.lookupLoc locWitness heapEnv with
                  | None -> None
                  | Some HRecd _ -> None
                  | Some HMu mu ->
                      if mu = muExists (* TODO more permissive test? *)
                      then Some (HeapEnv.removeLoc locWitness heapEnv)
                      else None))

let recdSub_ : ('a -> field -> typ -> typ -> 'a) -> 'a -> 'a
            -> recd_type -> recd_type -> 'a =
fun foo initSuccessResult failureResult rt1 rt2 ->
  let TRecd(width1,fts1) = rt1 in
  let TRecd(width2,fts2) = rt2 in
  let keysOk l1 l2 = List.for_all (fun (f,_) -> List.mem_assoc f l1) l2 in
  let widthOkay =
    match width1, width2 with
      | UnknownDomain, ExactDomain   -> false
      | _,             UnknownDomain -> keysOk fts1 fts2
      | ExactDomain,   ExactDomain   -> keysOk fts1 fts2 && keysOk fts2 fts1
  in
  if not widthOkay then failureResult
  else List.fold_left
         (fun acc (f,t2) -> let t1 = List.assoc f fts1 in foo acc f t1 t2)
         initSuccessResult fts2

let recdSub =
  recdSub_ (fun acc _ s t -> acc && sub s t) true false

let recdSubAndPack heapEnv =
  recdSub_
    (fun acc _ s t -> ifSome acc (fun heapEnv -> subAndPack heapEnv s t))
    (Some heapEnv) None

let heapSat : HeapEnv.t -> heap -> bool =
fun heapEnv heap ->
  List.for_all (fun (l,lb) ->
    match HeapEnv.lookupLoc l heapEnv, lb with
      (* TODO more permissive test? *)
      | Some(HRecd(rt1)), HRecd(rt2) -> rt1 = rt2
      | Some(HMu(mu1)), HMu(mu2) -> mu1 = mu2
      | _ -> false
  ) heap

let removeHeap : HeapEnv.t -> heap -> HeapEnv.t =
  List.fold_left (fun acc (l,_) -> HeapEnv.removeLoc l acc)

let addHeap : HeapEnv.t -> heap -> HeapEnv.t =
  List.fold_left (fun acc (l,lb) ->
    if HeapEnv.memLoc l acc
    then failwith (spr "addHeap: %s already in heap env" (strLoc l))
    else HeapEnv.addLoc l lb acc)

let rec join s t = match s, t with
  | s, t when s = t -> s
  | _, TAny | TAny, _ -> TAny
  | u, TBot | TBot, u -> u
  | TBase _, TBase _ -> tUnion [s; t]
  | TUnion l1, TUnion l2 -> tUnion (l1 @ l2)
  | TUnion l, u | u, TUnion l -> tUnion (u :: l)
  (* TODO *)
  | _ -> TAny

and joinRecdTypes : recd_type -> recd_type -> recd_type =
fun (TRecd(width1,fts1)) (TRecd(width2,fts2)) ->
  let fts =
    List.fold_left (fun acc (f,t1) ->
      if not (List.mem_assoc f fts2) then acc
      else let t2 = List.assoc f fts2 in (f, join t1 t2) :: acc
    ) [] fts1
  in
  let width =
    match width1, width2 with
      | ExactDomain, ExactDomain when List.length fts = List.length fts1 ->
          ExactDomain
      | _ ->
          UnknownDomain
  in
  TRecd (width, fts)

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
    LocMap.fold (fun l x acc ->
      if not (LocMap.mem l he2) then acc
      else
        match x, LocMap.find l he2 with
          | HRecd(rt1), HRecd(rt2) ->
              LocMap.add l (HRecd (joinRecdTypes rt1 rt2)) acc
          | x, y when x = y ->
              LocMap.add l x acc
          | _ ->
              failwith "joinLocs"
    ) he1 LocMap.empty
  in
  fun he1 he2 ->
    { HeapEnv.vars = joinVars he1.HeapEnv.vars he2.HeapEnv.vars;
      HeapEnv.locs = joinLocs he1.HeapEnv.locs he2.HeapEnv.locs; }

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

let unrollMuDef : mu_type -> (var * recd_type) -> recd_type =
fun mu -> function
  | "_", rt -> rt
  | x, TRecd(width,fts) ->
      let foo =
        mapTyp (function
                 | TExistsRef(l,MuVar(y)) when x = y -> TExistsRef (l, mu)
                 | t -> t) in
      let fts = List.map (fun (f, t) -> (f, foo t)) fts in
      TRecd (width, fts)

let unrollMu : TypeEnv.t -> mu_type -> recd_type =
fun typeEnv mu ->
  match mu with
    | Mu(x,rt) -> unrollMuDef mu (x,rt)
    | MuAbbrev(t,[]) ->
        (match TypeEnv.lookupTyAbbrev t typeEnv with
          | Some([],Mu(x,rt)) -> unrollMuDef mu (x,rt)
          | None -> failwith "unrollMu 1"
          | _ -> failwith "unrollMu 2")
    | MuAbbrev _ -> failwith "unrollMu with type args"
    | MuVar _ -> failwith "unrollMu: var wasn't substituted"

let pack : TypeEnv.t -> HeapEnv.t -> loc -> recd_type -> mu_type
        -> HeapEnv.t option =
fun typeEnv heapEnv l rt mu ->
  let rtGoal = unrollMu typeEnv mu in
  ifSome (recdSubAndPack heapEnv rt rtGoal)
    (fun heapEnv -> Some (HeapEnv.addLoc l (HMu mu) heapEnv))
    (* recdSubAndPack removed witnesses, so now just fold the top loc *)

let eagerUnpack : recd_type -> (loc_var list * recd_type) =
fun (TRecd(width,fts)) ->
  let existentialLocs = ref [] in
  let foo = function
    | TExistsRef(l,mu) ->
        let l = genLocVar () in
        let _ = existentialLocs := l :: !existentialLocs in
        TRefLoc (LVar l)
    | t -> t
  in
  let fts = List.map (fun (f,t) -> (f, mapTyp foo t)) fts in
  (List.rev !existentialLocs, TRecd (width, fts))

let singleRefOf : typ -> loc option =
function
  | TMaybe(TRefLoc(l)) -> Some l
  | TUnion(ts) ->
      let ls =
        List.fold_left
          (fun acc -> function TRefLoc(l) -> l :: acc | _ -> acc) [] ts in
      (match ls with
        | [l] -> Some l
        | []  -> None
        | _   -> None) (* don't want unions with multiple ref types *)
  | _ -> None

let refCast : typ -> exp option =
fun t ->
  match singleRefOf t with
    | None -> None
    | Some _ ->
        let x = "L_" in
        let tx = TRefLoc (LVar x) in
        Some (ePolyCast (([x], [TMaybe tx], []), ([], tx, [])))

let synthesizeRecd : recd_type -> exp option =
fun (TRecd(width,fts)) ->
  let foo = function
    | TAny          
    | TBase TNum      -> Some (eInt 0)
    | TBase TStr      -> Some (eStr "")
    | TBase TBool     -> Some (eBool true)
    | TBase TUndef    -> Some eUndef
    | TBase TNull     -> Some eNull
    | TMaybe _        -> Some eNull
    | _               -> None
  in
  let maybeObj =
    List.fold_left (fun acc (f,t) ->
      match acc, foo t with
        | Some fes, Some e -> Some ((f, e) :: fes)
        | _                -> None
    ) (Some []) fts
  in
  match maybeObj with
    | Some fes -> Some (eObj (List.rev fes))
    | None     -> None

let synthesizable : TypeEnv.t -> loc_binding -> bool =
fun typeEnv lb ->
  let rt = match lb with HRecd rt -> rt | HMu mu -> unrollMu typeEnv mu in
  match synthesizeRecd rt with
    | Some _ -> true
    | None   -> false

type loc_subst = (loc_var * loc) list

(* in addition to a substitution, computes a heap environment in case
   dummy objects were synthesized for unreachable locations *)

let computeLocSubst : TypeEnv.t -> HeapEnv.t
                   -> loc_var list -> typ list -> typ list -> heap
                   -> (loc_subst * HeapEnv.t) option =
fun typeEnv heapEnv locVars tsActual tsExpected hExpected ->
  List.fold_left (fun acc locVar_i ->
    ifSome acc (fun (subst,heapEnv) ->
      let maybeLocArgAndHeapEnv =
        List.fold_left (fun acc (tActual,tExpected) ->
          ifNone acc (fun () ->
            match tActual, tExpected with
             | TMaybe TRefLoc l, TMaybe TRefLoc LVar lv
             | TRefLoc l, TMaybe TRefLoc LVar lv
             | TRefLoc l, TRefLoc LVar lv when lv = locVar_i ->
                 let _ = pr "%s |-> %s\n" locVar_i (strLoc l); flush stdout in
                 Some (l, heapEnv)
             | TBase TNull, TMaybe TRefLoc LVar lv 
               when List.mem_assoc (LVar lv) hExpected ->
                 let lb = List.assoc (LVar lv) hExpected in
                 if not (synthesizable typeEnv lb) then None
                 else
                   let lv = genLocVar ~name:"dummy" () in
                   let heapEnv = HeapEnv.addLoc (LVar lv) lb heapEnv in
                   Some (LVar lv, heapEnv)
             | _ ->
                 None)
        ) None (List.combine tsActual tsExpected)
      in
      match maybeLocArgAndHeapEnv with
       | None -> None
       | Some (locArg_i, heapEnv) ->
           Some (subst @ [(locVar_i,locArg_i)], heapEnv))
  ) (Some ([], heapEnv)) locVars

let applySubst : loc_subst -> typ -> typ =
fun subst ->
  mapTyp (function
    | TRefLoc LVar x when List.mem_assoc x subst -> TRefLoc (List.assoc x subst)
    | t -> t
  )

let applySubstToHeap : loc_subst -> heap -> heap =
fun subst ->
  List.map (fun (l,lb) ->
    let l =
      match l with
       | LVar lv when List.mem_assoc lv subst -> List.assoc lv subst
       | _ -> l
    in (l, lb) (* TODO need to recurse into bindings? *)
  )

let freshen : loc_var list -> loc_subst =
fun xs ->
  let freshenOne x = genLocVar ~name:x () in
  let ys = List.map freshenOne xs in
  List.combine xs (List.map (fun y -> LVar y) ys)

let transitiveAssumeVars f heapEnv =
  let rec doOne f acc =
    let acc = Vars.add f acc in
    match HeapEnv.lookupVar f heapEnv with
      | Some(OpenArrow(rely,_)) ->
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

let addPath lv path =
  match lv with
    | LvalVar x -> LvalPath (x, path)
    | LvalPath (x, path0) -> LvalPath (x, path0 @ path)

type 'a tri_result = Yes | No | YesIf of 'a

let resultAppend
    : 'a list tri_result -> 'a list tri_result -> 'a list tri_result =
fun x y -> match x, y with
  | No       , _        -> No
  | Yes      , _        -> y
  | YesIf _  , No       -> No
  | YesIf l  , Yes      -> YesIf l
  | YesIf l1 , YesIf l2 -> YesIf (l1 @ l2)

let resultAdd 
    : 'a list tri_result -> 'a -> 'a list tri_result =
fun x y -> match x with
  | No      -> No
  | Yes     -> YesIf [y]
  | YesIf l -> YesIf (l @ [y])

type path             = field list
type path_list        = (path * mu_type) list
type rooted_path_list = loc * mu_type * path_list

let rec subAndFold
    : TypeEnv.t -> HeapEnv.t -> path -> typ -> typ
   -> path_list tri_result =
fun typeEnv heapEnv path ->
  sub_ (fun () -> Yes)
       (fun () -> No)
       (Some (fun (locWitness, _, muExists) ->
                let rt2 = unrollMu typeEnv muExists in
                match HeapEnv.lookupLoc locWitness heapEnv with
                  | None -> No
                  | Some HRecd rt1 ->
                      let res = recdSubAndFold typeEnv heapEnv path rt1 rt2 in
                      resultAppend res (YesIf [(path, muExists)])
                  | Some HMu mu ->
                      if mu = muExists (* TODO more permissive test? *)
                      then Yes
                      else No))

and recdSubAndFold
    : TypeEnv.t -> HeapEnv.t -> path -> recd_type -> recd_type
   -> path_list tri_result =
fun typeEnv heapEnv path ->
  recdSub_ (fun acc f s t ->
    resultAppend acc (subAndFold typeEnv heapEnv (path @ [f]) s t)
  ) Yes No

let heapSat_
    : TypeEnv.t -> HeapEnv.t -> heap -> rooted_path_list list tri_result =
fun typeEnv heapEnv heap ->
  List.fold_left (fun acc (l,lb) ->
    match HeapEnv.lookupLoc l heapEnv, lb, !Settings.castInsertionMode with
      (* TODO more permissive tests? *)
      | Some HRecd rt1, HRecd rt2, _ when rt1 = rt2 -> acc
      | Some HMu mu1, HMu mu2, _ when mu1 = mu2 -> acc
      | Some HRecd rt1, HMu mu, true ->
          let root = [] in
          let rt2 = unrollMu typeEnv mu in
          (match recdSubAndFold typeEnv heapEnv root rt1 rt2 with
            | YesIf pathList -> resultAdd acc (l, mu, pathList)
            | Yes            -> resultAdd acc (l, mu, [])
            | No             -> No)
      | _ -> No
  ) Yes heap

type inferred_folds = bool * exp list (* true if all folds can be lifted out *)

let inferFolds
    : TypeEnv.t -> HeapEnv.t -> (exp * typ) list -> rooted_path_list list
   -> inferred_folds option =
fun typeEnv heapEnv ets lists ->

  let makeFolds lvRoot locRoot muRoot pathLists =
    (* want longest paths first, so that inner objects are folded
       up before outer ones *)
    let pathLists = List.rev (List.sort compare pathLists) in
    let pathLists = pathLists @ [([], muRoot)] in
    List.map
      (fun (path,mu) -> eFold mu (eLval (addPath lvRoot path)))
      pathLists in

  let foldFromArgs (locRoot, muRoot, pathLists) : exp list option =
    List.fold_left (fun acc (e,t) ->
      match acc, t, lvalOf e with
        | Some _, _, _ -> acc
        | None, TRefLoc l, Some lv when l = locRoot ->
            Some (makeFolds lv locRoot muRoot pathLists)
        | _ -> None
    ) None ets in

  let foldFromEnv (locRoot, muRoot, pathLists) : exp list option =
    VarMap.fold (fun x t acc ->
      ifNone acc (fun () ->
        match t with
          | Val TRefLoc l | InvariantRef TRefLoc l when l = locRoot ->
              Some (makeFolds (LvalVar x) locRoot muRoot pathLists)
          | StrongRef ->
              (match HeapEnv.lookupVar x heapEnv with
                 | Some Typ TRefLoc l when l = locRoot ->
                     Some (makeFolds (LvalVar x) locRoot muRoot pathLists)
                 | _ -> None)
          | _ -> None)
    ) typeEnv.TypeEnv.bindings None in

  List.fold_left (fun acc rootedPathList ->
    match acc, foldFromArgs rootedPathList, foldFromEnv rootedPathList with
      | Some (canLiftAll, l), Some folds, _ ->
          Some (canLiftAll && true, l @ folds)
      | Some (canLiftAll, l), None, Some folds ->
          Some (canLiftAll && false, l @ folds)
      | _ ->
          None
  ) (Some (true, [])) lists  

let retryStmtForFolds folds =
  let sFolds = List.map sTcInsert (List.map sExp folds) in
  let sRetry = sSeq sFolds in
  sRetry

let inlineExpForFolds folds e =
  let x = genSym () in
  let rec foo = function
    | []    -> eVar x
    | e::es -> eLet "_" e (foo es)
  in
  eTcInsert (eLet x e (foo folds))

let rec sequenceOfTcInserts : stmt -> bool =
function
  | {stmt=SSeq({stmt=STcInsert _},s)} -> sequenceOfTcInserts s
  | {stmt=STcInsert _}                -> true
  | _                                 -> false

let heapSatWithFolds
    : TypeEnv.t -> HeapEnv.t -> heap -> (exp * typ) list
   -> inferred_folds tri_result =
fun typeEnv heapEnv hGoal ets ->
  match heapSat_ typeEnv heapEnv hGoal with
    | No -> No
    | Yes -> Yes
    | YesIf rootedPathLists ->
        (match inferFolds typeEnv heapEnv ets rootedPathLists with
           | None -> No
           | Some (canLiftAll, folds) -> YesIf (canLiftAll, folds))

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
  if sub s t then
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

  | EAs({exp=EFun(xs,body)},Typ(TArrow(([],tArgs,[]),([],tRet,[])))) ->
      tcAnnotatedFun typeEnv heapEnv xs body RelySet.empty tArgs tRet

  | EAs({exp=EFun(xs,body)},OpenArrow(r,(([],tArgs,[]),([],tRet,[])))) ->
      tcAnnotatedFun typeEnv heapEnv xs body r tArgs tRet

  | EAs({exp=EFun(xs,body)},Typ(TArrow(arrow))) ->
      tcAnnotatedPolyFun typeEnv heapEnv xs body RelySet.empty arrow

  | EAs({exp=EFun(xs,body)},OpenArrow(r,arrow)) ->
      tcAnnotatedPolyFun typeEnv heapEnv xs body r arrow

  | ECast(arrow) ->
      Ok (exp, (Typ (TArrow arrow), heapEnv, MoreOut.empty))

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
            | Typ(TArrow(([],tArgs,[]),([],tRet,[]))) ->
                tcApp1 typeEnv heapEnv outFun eFun eArgs tArgs tRet
            | Typ(TArrow(arrow)) ->
                tcAppPoly typeEnv heapEnv outFun eFun eArgs arrow
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
                  | Some(HRecd(rt)) ->
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
                            else Ok (eGet e1 e2, (Typ TAny, heapEnv, out)))
                  | Some(HMu(Mu _ as mu))
                  | Some(HMu(MuAbbrev _ as mu)) ->
                      let err = spr "need to unfold: %s" (strMu mu) in
                      (match lvalOf e1 with
                        | Some(lv) ->
                            (* let sRetry = sAssignLval lv (eUnfold mu (eLval lv)) in *)
                            let sRetry = sExp (eUnfold mu (eLval lv)) in
                            Err (eGet (eTcErrRetry err e1 sRetry) e2)
                        | _ ->
                            Err (eGet (eTcErr err e1) e2))
                  | Some(HMu(MuVar _)) ->
                      failwith "tc EObjRead: mu var wasn't unrolled?")
            | Typ(t), _ ->
                let err = spr "not a ref type: %s" (strTyp t) in
                (match lvalOf e1, refCast t with
                  | Some(lv), Some(cast) ->
                      let sRetry = sAssignLval lv (eApp cast [eLval lv]) in
                      Err (eGet (eTcErrRetry err e1 sRetry) e2)
                  (* could add this case: | None, Some(cast) -> *)
                  | _ ->
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
                  | Some(HMu _) -> Err (eFold mu (eTcErr "not recd type" e))
                  | Some(HRecd(rt)) ->
                      (match pack typeEnv heapEnv l rt mu with
                        | Some(heapEnv) ->
                            Ok (eFold mu e, (addExists locs pt, heapEnv, out))
                        | None ->
                            let err = spr "can't pack:\n\n %s\n\n %s\n\n"
                              (strRecdType rt)
                              (strRecdType (unrollMu typeEnv mu)) in
                            Err (eFold mu (eTcErr err e))))
            | _ ->
                let err = spr "not a reference type:\n%s\n" (strPreTyp pt) in
                Err (eFold mu (eTcErr err e)))

  | EUnfold(mu,e) ->
      run tcExp (typeEnv, heapEnv, e)
        (fun e -> Err (eUnfold mu e))
        (fun e (pt,heapEnv,out) ->
           let (locs,pt) = stripExists pt in
           match pt with
            | Typ(TRefLoc(l)) ->
                (match HeapEnv.lookupLoc l heapEnv with
                  | None -> Err (eUnfold mu (eTcErr "not in heap" e))
                  | Some(HRecd _) -> Err (eUnfold mu (eTcErr "not mu-type" e))
                  | Some(HMu(mu)) ->
                      let rt = unrollMu typeEnv mu in
                      let (existentialLocs,rt) = eagerUnpack rt in
                      let pt = addExists (locs @ existentialLocs) pt in
                      let heapEnv = HeapEnv.addLoc l (HRecd rt) heapEnv in
                      let heapEnv =
                        List.fold_left
                          (fun acc li -> HeapEnv.addLoc (LVar li) (HMu mu) acc)
                          heapEnv existentialLocs
                      in
                      Ok (eUnfold mu e, (pt, heapEnv, out)))
            | _ ->
                let err = spr "not a reference type:\n%s\n" (strPreTyp pt) in
                Err (eUnfold mu (eTcErr err e)))

  | ETcInsert(e) ->
      run tcExp (typeEnv, heapEnv, e)
        (fun e -> Err (eTcInsert e))
        (fun e stuff -> Ok (eTcInsert e, stuff))

  | ELet(x,e1,e2) ->
      if x <> "_" && TypeEnv.memVar x typeEnv
      then Err (eLet x (eTcErr (spr "var [%s] is already scope" x) e1) e2)
      else
        run tcExp (typeEnv, heapEnv, e1)
          (fun e1 -> Err (eLet x e1 e2))
          (fun e1 (pt1,heapEnv,out1) ->
             let (locs1,pt1) = stripExists pt1 in
             match pt1 with
              | Exists _ -> assert false
              | OpenArrow _ -> Err (eLet x (eTcErr "open type" e1) e2)
              | Typ t1 ->
                  let typeEnv =
                    if x = "_" then typeEnv
                    else TypeEnv.addVar x (Val t1) typeEnv
                  in
                  run tcExp (typeEnv, heapEnv, e2)
                    (fun e2 -> Err (eLet x e1 e2))
                    (fun e2 (pt2,heapEnv,out2) ->
                       let out = MoreOut.combine out1 out2 in
                       let pt2 = addExists locs1 pt2 in
                       Ok (eLet x e1 e2, (pt2, heapEnv, out))))

  | EAs(_,_) ->
      errE "non-function value in ascription" exp

  | ETcErr _ ->
      failwith "tc ETcErr"

and tcBareFun typeEnv heapEnv xs body =

  let typeEnv = TypeEnv.addRetWorld ([], TAny, []) typeEnv in
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
        | OpenArrow(_,arrow) ->
            let tArrow = TArrow arrow in
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
            let ptArrow = finishArrow rely (([], tArgs, []), ([], tRet, [])) in
            let out = { out with MoreOut.retTypes = Types.empty } in
            Ok (eAs (eFun xs body) ptArrow, (ptArrow, heapEnv, out)))

(* simpler version of tcAnnotatedFunPoly for pure arrows *)
and tcAnnotatedFun typeEnv heapEnv xs body rely tArgs tRet =
  let origArrow = OpenArrow (rely, (([], tArgs, []), ([], tRet, []))) in
  if List.length xs <> List.length tArgs
    then failwith "add handling for len(actuals) != len(formals)";
  let typeEnv = TypeEnv.addRetWorld ([], tRet, []) typeEnv in
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
            let ptArrow = finishArrow rely (([], tArgs, []), ([], tRet, [])) in
            if sub tBody tRet then
              Ok (eAs (eFun xs body) ptArrow, (ptArrow, heapEnv, MoreOut.empty))
            else
              let err = "fun has bad fall-thru type" in
              Err (eAs (eFun xs (sTcErr err body)) origArrow))

and tcAnnotatedPolyFun typeEnv heapEnv xs body rely arrow =
  let ((allLocs,tArgs,h1),(someLocs,tRet,h2)) = arrow in
  let ptArrow = finishArrow rely arrow in
  if not (wellFormed typeEnv ptArrow) then
    Err (eTcErr "arrow not well-formed" (eAs (eFun xs body) ptArrow))
  else if List.length xs != List.length tArgs then
    failwith "add handling for len(actuals) != len(formals)"
  else
    let typeEnv =
      RelySet.fold
        (fun (x,t) acc -> TypeEnv.addVar x (InvariantRef t) acc) rely typeEnv
    in
    let typeEnv = TypeEnv.addLocVars allLocs typeEnv in
    let typeEnv = TypeEnv.addRetWorld (someLocs, tRet, h2) typeEnv in
    let (typeEnv,heapEnvFun) =
      List.fold_left (fun (acc1,acc2) (x,tArg) ->
        let acc1 = TypeEnv.addVar x StrongRef acc1 in
        let acc2 = HeapEnv.addVar x (Typ tArg) acc2 in
        (acc1, acc2)
      ) (typeEnv, HeapEnv.empty) (List.combine xs tArgs)
    in
    let heapEnvFun =
      List.fold_left (fun acc (l,lb) ->
        if HeapEnv.memLoc l acc
        then failwith "tcAnnotatedPolyFun: loc already bound"
        else HeapEnv.addLoc l lb acc
      ) heapEnvFun h1
    in
    run tcStmt (typeEnv, heapEnvFun, body)
      (fun body -> Err (eAs (eFun xs body) ptArrow))
      (fun body (pt,heapEnvFunOut,_) ->
         let (locs,pt) = stripExists pt in
         match pt with
          | Typ TBot ->
               let stuff = (ptArrow, heapEnv, MoreOut.empty) in
               Ok (eAs (eFun xs body) ptArrow, stuff)
          | Typ(tBody) ->
              let substAndHeapEnv =
                computeLocSubst typeEnv heapEnv someLocs [tBody] [tRet] h2 in
              (match substAndHeapEnv with
                | None ->
                    let err = "couldn't infer output instantiations" in
                    Err (eAs (eFun xs (sTcErr err body)) ptArrow)
                | Some (subst, heapEnv) ->
                    let tRet = applySubst subst tRet in
                    let h2 = applySubstToHeap subst h2 in
                    if not (sub tBody tRet) then
                      let err = "bad fall-thru type" in
                      Err (eAs (eFun xs (sTcErr err body)) ptArrow)
                    else if not (heapSat heapEnvFunOut h2) then
                      let err = spr "bad fall-thru heap environment:\n\n%s\n\n%s\n\n"
                        (HeapEnv.strLocs heapEnvFunOut) (strHeap h2) in
                      Err (eAs (eFun xs (sTcErr err body)) ptArrow)
                    else
                      let stuff = (ptArrow, heapEnv, MoreOut.empty) in
                      Ok (eAs (eFun xs body) ptArrow, stuff))
          | _ ->
              let err = "type of body is open" in
              Err (eAs (eFun xs (sTcErr err body)) ptArrow))

(* could rely on tcAppPoly for simple arrows, but tcApp1 is more direct *)
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

and tcAppPoly typeEnv heapEnv outFun eFun eArgs arrow =
  let ((allLocs,tArgsExpected,h1),(someLocs,tRet,h2)) = arrow in
  let (eArgs,maybeOutput) =
    List.fold_left (fun (eArgs,maybeOutput) eArg ->
      match maybeOutput with
       | None -> (eArgs @ [eArg], None)
       | Some(tArgsActual,existentialLocs,heapEnv,out) ->
           run tcExp (typeEnv, heapEnv, eArg)
             (fun eArg -> (eArgs @ [eArg], None))
             (fun eArg (ptActual,heapEnv,out') ->
                let (locs,ptActual) = stripExists ptActual in
                match ptActual with
                 | Typ(tActual) ->
                     let tArgsActual = tArgsActual @ [tActual] in
                     let existentialLocs = existentialLocs @ locs in
                     let out = MoreOut.combine out out' in
                     let stuff = (tArgsActual, existentialLocs, heapEnv, out) in
                     (eArgs @ [eArg], Some stuff)
                 | _ ->
                     (eArgs @ [eArg], None))
    ) ([], Some ([], [], heapEnv, outFun)) eArgs
  in
  match maybeOutput with
   | None -> Err (eApp eFun eArgs)
   | Some(tArgsActual,existentialLocs,heapEnv,out) ->
       let substAndHeapEnv =
         computeLocSubst typeEnv heapEnv allLocs tArgsActual tArgsExpected h1 in
       match substAndHeapEnv with
        | None -> Err (eTcErr "couldn't infer instantiations" (eApp eFun eArgs))
        | Some (subst, heapEnv) ->
            let tArgsExpected = List.map (applySubst subst) tArgsExpected in
            let obligations = List.combine tArgsActual tArgsExpected in
            let (eArgs,allOk) =
              List.fold_left (fun (eArgs,acc) (eArg,(tActual,tExpected)) ->
                if acc = false then (eArgs @ [eArg], false)
                else if sub tActual tExpected then (eArgs @ [eArg], true)
                else let (s1,s2) = (strTyp tActual, strTyp tExpected) in
                     let err = spr "not subtype:\n%s\n%s\n" s1 s2 in
                     (eArgs @ [eTcErr err eArg], false)
              ) ([], true) (List.combine eArgs obligations)
            in
            let h1 = applySubstToHeap subst h1 in
            if not allOk then
              Err (eApp eFun eArgs)
            else if not (heapSat heapEnv h1) then
              let err = "input heap not satisfied" in
              Err (eTcErr err (eApp eFun eArgs))
            else
              let substFresh = freshen someLocs in
              let tRet = applySubst (subst @ substFresh) tRet in 
              let h2 = applySubstToHeap (subst @ substFresh) h2 in
              let heapEnv = removeHeap heapEnv h1 in
              let heapEnv = addHeap heapEnv h2 in
              let ptRet = addExists existentialLocs (Typ tRet) in
              Ok (eApp eFun eArgs, (ptRet, heapEnv, out))

and tcApp2 typeEnv heapEnv outFun eFun eArgs tFun =
  let tAnys = List.map (function _ -> TAny) eArgs in
  run coerce (eFun, tFun, pureArrow tAnys TAny)
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
        let heapEnv = HeapEnv.addLoc (LVar locObj) (HRecd tRecd) heapEnv in
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
          | Err _, _ when sequenceOfTcInserts sRetry -> (* don't re-wrap *)
              tcStmt (typeEnv, heapEnv, sSeq [sRetry; stmt])
          | Err _, _ ->
              tcStmt (typeEnv, heapEnv, sSeq [sTcInsert sRetry; stmt])
      ) (Err stmtErr) retryStmts
    end

and __tcStmt (typeEnv, heapEnv, stmt) = match stmt.stmt with

  | SExp(e) ->
      run tcExp (typeEnv, heapEnv, e)
        (fun e -> Err (sExp e))
        (fun e (_,heapEnv,out) -> Ok (sExp e, (Typ tUndef, heapEnv, out)))

  | SReturn(e) ->
      (* not just calling tcCoerce, because want to add synthesized
         return type to output *)
      let heapEnvOrig = heapEnv in
      let eOrig = e in
      run tcExp (typeEnv, heapEnv, e)
        (fun e -> Err (sRet e))
        (fun e (pt,heapEnv,out) ->
           let (locs,pt) = stripExists pt in
           match pt with
            | Exists _ -> assert false
            | OpenArrow _ -> Err (sTcErr "return exp has open type" (sRet e))
            | Typ(t) ->
                let (someLocs,tGoal,hGoal) = TypeEnv.lookupRetWorld typeEnv in
                let substAndHeapEnv =
                  computeLocSubst typeEnv heapEnv someLocs [t] [tGoal] hGoal in
                (match substAndHeapEnv with
                  | None ->
                      let err = "couldn't infer instantations at return" in
                      Err (sRet (eTcErr err e))
                  | Some (subst, heapEnv) ->
                      let tGoal = applySubst subst tGoal in
                      let hGoal = applySubstToHeap subst hGoal in
                      run coerceOrFold (true, typeEnv, heapEnv, e, t, tGoal)
                        (fun e -> Err (sRet e))
                        (fun e (heapEnv,out') ->
                           let err = "expected heap not satisfied" in
                           let ets = [(e,t)] in
                           match heapSatWithFolds typeEnv heapEnv hGoal ets with
                             | No ->
                                 Err (sRet (eTcErr err e))
                             | YesIf (true, folds) ->
                                 let sRetry = retryStmtForFolds folds in
                                 Err (sRet (eTcErrRetry err e sRetry))
                             | YesIf (false, folds) ->
                                 (* inline backtracking *)
                                 let e' = inlineExpForFolds folds eOrig in
                                 run tcStmt (typeEnv, heapEnvOrig, sRet e')
                                   (fun _ -> Err (sRet (eTcErr err e)))
                                   (fun s stuff -> Ok (s, stuff))
                             | Yes ->
                                 let out = MoreOut.combine out out' in
                                 let out = MoreOut.addRetType t out in
                                 let ptBot = addExists locs (Typ TBot) in
                                 Ok (sRet e, (ptBot, heapEnv, out)))))

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
      (* calling __tcStmt to avoid backtracking, since want failures to
         propagate to the caller of tcStmt on the entire sequence statement *)
      run __tcStmt (typeEnv, heapEnv, s1)
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
      run tcCoerceLocally (typeEnv, heapEnv, e1, tBool)
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
      run tcCoerceLocally (typeEnv, heapEnv, e, tBool)
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
            if not (sub tCurrentX tGoalX) then
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
                 | Some(OpenArrow(r,arrow)) ->
                     let accR = RelySet.union accR r in
                     let accG = RelySet.add (x, TArrow arrow) accG in
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
                  | Some(HRecd(rt)) ->
                      let rt' = TRecd (ExactDomain, [(f,t3)]) in
                      let rt = extendRecdType rt rt' in
                      let heapEnv = HeapEnv.addLoc l (HRecd rt) heapEnv in
                      Ok (sSet e1 e2 e3, (addExists locs3 (Typ t3), heapEnv, out))
                  | Some(HMu(Mu _ as mu))
                  | Some(HMu(MuAbbrev _ as mu)) ->
                      let err = spr "need to unfold: %s" (strMu mu) in
                      (match lvalOf e1 with
                        | Some(lv) ->
                            let sRetry = sExp (eUnfold mu (eLval lv)) in
                            Err (sSet (eTcErrRetry err e1 sRetry) e2 e3)
                        | _ ->
                            Err (sSet (eTcErr err e1) e2 e3))
                  | Some(HMu(MuVar _)) ->
                      failwith "tc EObjAssign: mu var wasn't expanded?")
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

and tcCoerce args          = _tcCoerce true args
and tcCoerceLocally args   = _tcCoerce false args

and _tcCoerce hoistCasts (typeEnv, heapEnv, e, tGoal) =
  run tcExp (typeEnv, heapEnv, e)
    (fun e -> Err e)
    (fun e (pt,heapEnv,out) ->
       let (_,pt) = stripExists pt in (* TODO okay to throw away locs? *)
       match pt with
        | Exists _ -> assert false
        | OpenArrow _ -> errE "cannot coerce from open arrow" e
        | Typ(t) ->
            run coerceOrFold (hoistCasts, typeEnv, heapEnv, e, t, tGoal)
              (fun e -> Err e)
              (fun e (heapEnv,out') ->
                 let out = MoreOut.combine out out' in
                 Ok (e, (heapEnv, out))))

and coerceOrFold (hoistCasts, typeEnv, heapEnv, e, t, tGoal) =
  run coerce (e, t, tGoal)
    (fun eErr ->
       match t, tGoal, hoistCasts, lvalOf e with
        (* TODO
        | TRefLoc _, TMaybe(TRefMu(mu)), true, Some(lv)
        | TRefLoc _, TRefMu(mu), true, Some(lv) ->
            let sRetry = sExp lv (eFold mu (eLval lv)) in
            Err (eTcErrRetry "blah" e sRetry)
        | TRefLoc _, TMaybe(TRefMu(mu)), _, _
        | TRefLoc _, TRefMu(mu), _, _ ->
            run tcExp (typeEnv, heapEnv, eFold mu e)
              (fun _ -> Err e)
              (fun _ (_,heapEnv,out) ->
                 Ok (eTcInsert (eFold mu e), (heapEnv, out)))
        *)
        | _ ->
            Err eErr)
    (fun eOk insertedCast ->
       (* if coercion inserted, hoist it out to an assignment if
          possible rather than inserting the cast locally *)
       match insertedCast && hoistCasts, lvalOf e with
        | true, Some(lv) ->
            let sRetry = sAssignLval lv eOk in
            Err (eTcErrRetry "tcCoerce backtracking" e sRetry)
        | _ ->
            Ok (eOk, (heapEnv, MoreOut.empty)))

let removeTcInserts prog =
  mapStmt (* keep in sync with what tc can insert *)
    (function
      | EApp({exp=ETcInsert{exp=ECast _}},[eArg]) -> eArg.exp
      | ETcInsert({exp=EFold(_,e)}) -> e.exp
      | ETcInsert({exp=ELet(_,e,_)}) -> e.exp
      | e -> e)
    (function
      | STcInsert({stmt=SClose(_,s)})
      | STcInsert({stmt=SVarInvariant(_,_,s)})
      | STcInsert({stmt=SSeq({stmt=SExp _},s)})
      | STcInsert({stmt=SSeq({stmt=SVarAssign _},s)})
      | STcInsert({stmt=SSeq({stmt=SObjAssign _},s)}) -> s.stmt
      | STcInsert({stmt=SExp _})
      | STcInsert({stmt=SVarAssign _})
      | STcInsert({stmt=SObjAssign _}) -> sSkip.stmt
      | s -> s)
    prog

let typecheck prog =
  clearLocVarCounter ();
  let prog =
    if !Settings.castInsertionMode
    then removeTcInserts prog (* remove [...] expressions and statements *)
    else prog
  in
  match tcStmt (TypeEnv.empty, HeapEnv.empty, prog) with
   | Ok(prog,_) -> Ok (prog, ())
   | Err(prog)  -> Err prog

