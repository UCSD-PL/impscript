
open Lang
open LangUtils
open Printer

module StrMap = Utils.StrMap

let ifSome opt f = match opt with Some(x) -> f x | _ -> opt

let ifNone opt f = match opt with None -> f () | _ -> opt

let liftHeapBinding = function
  | HRecd rt -> HERecd rt
  | HMu mu   -> HEMu mu

let strHeapEnvBinding (l, heb) =
  let (s1, s2) = AcePrinter.strPairHeapEnvBinding (l, heb) in
  spr "%s%s" s1 s2

module TypeEnv = struct

  type t = type_env

  let empty : t =
    { bindings = VarMap.empty;
      loc_vars = Vars.empty;
      mu_vars = Vars.empty;
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

  let memLocVar : var -> t -> bool =
  fun x typeEnv ->
    Vars.mem x typeEnv.loc_vars

  let addMuVar : ty_var -> t -> t =
  fun x typeEnv ->
    { typeEnv with mu_vars = Vars.add x typeEnv.mu_vars }

  let memMuVar : ty_var -> t -> bool =
  fun x typeEnv ->
    Vars.mem x typeEnv.mu_vars

  let addMuAbbrev : ty_abbrev -> (ty_var list * mu_type) -> t -> t =
  fun x def typeEnv ->
    { typeEnv with ty_abbrevs = StrMap.add x def typeEnv.ty_abbrevs }

  let lookupMuAbbrev : ty_abbrev -> t -> (ty_var list * mu_type) option =
  fun x typeEnv ->
    if StrMap.mem x typeEnv.ty_abbrevs
    then Some (StrMap.find x typeEnv.ty_abbrevs)
    else None

end

module HeapEnv = struct

  type t = heap_env

  let empty : t = emptyHeapEnv

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

  let addLoc : loc -> heap_env_binding -> t -> t =
  fun l lb he ->
    { he with locs = LocMap.add l lb he.locs }

  let lookupLoc : loc -> t -> heap_env_binding option =
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
      LocMap.fold
        (fun l heb acc -> strHeapEnvBinding (l,heb) :: acc) he.locs []
    in
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

let (genLocConst,clearLocConstCounter) =
  let i = ref 0 in
  (fun ?(name="") () -> incr i; spr "lJoin%s_%d" name !i),
  (fun () -> i := 0)

(* be careful not to generate "L1", "L2", etc.
   since these are likely to appear in source programs *)
let (genLocVar,clearLocVarCounter) =
  let i = ref 0 in
  (fun ?(name="anon") () -> incr i; spr "L%d_%s" !i name),
  (fun () -> i := 0)

let (genSym,clearTmpCounter) =
  let i = ref 0 in
  (fun ?(name="") () -> incr i; spr "__%s%d" name !i),
  (fun () -> i := 0)

let projTyp = function
  | Typ(t) -> t
  | _ -> failwith "projTyp"

let wfLoc : TypeEnv.t -> loc -> bool =
fun typeEnv -> function
  | LConst _ -> true
  | LVar x   -> TypeEnv.memLocVar x typeEnv

let rec wfPreType : TypeEnv.t -> pre_type -> bool =
fun typeEnv -> function
  | Typ t                -> wfTyp typeEnv t
  | OpenArrow (r, arrow) -> wfRely typeEnv r && wfArrow typeEnv arrow
  | Exists (l, pt)       -> wfPreType (TypeEnv.addLocVar l typeEnv) pt

and wfTyp : TypeEnv.t -> typ -> bool =
fun typeEnv -> function
  | TBase _            -> true
  | TAny | TBot        -> true
  | TUnion ts          -> List.for_all (wfTyp typeEnv) ts
  | TRefLoc l          -> wfLoc typeEnv l
  | TMaybe t           -> wfTyp typeEnv t
  | TExistsRef (_, mu) -> wfMuType typeEnv mu
  | TArrow arrow       -> wfArrow typeEnv arrow
  | TPlaceholder       -> failwith "wfTyp TPlaceholder shouldn't appear"

and wfArrow : TypeEnv.t -> arrow -> bool =
fun typeEnv ((allLocs,tArgs,h1), (someLocs,tRet,h2)) ->
  let typeEnv1 = TypeEnv.addLocVars allLocs typeEnv in
  let typeEnv2 = TypeEnv.addLocVars someLocs typeEnv1 in
    List.for_all (wfTyp typeEnv1) tArgs
      && wfHeap typeEnv1 h1
      && wfTyp typeEnv2 tRet
      && wfHeap typeEnv2 h2

and wfMuType : TypeEnv.t -> mu_type -> bool =
fun typeEnv -> function
  | Mu (x, rt) -> wfRecdType (TypeEnv.addMuVar x typeEnv) rt
  | MuVar x    -> TypeEnv.memMuVar x typeEnv
  | MuAbbrev (x, ts) ->
      (match TypeEnv.lookupMuAbbrev x typeEnv with
        | Some _ -> List.for_all (wfTyp typeEnv) ts
        | None   -> false)

and wfRecdType : TypeEnv.t -> recd_type -> bool =
fun typeEnv (TRecd (_, fts)) ->
  let (fs,ts) = List.split fts in
  fs = Utils.removeDupes fs && List.for_all (wfTyp typeEnv) ts

and wfHeap : TypeEnv.t -> heap -> bool =
fun typeEnv ->
  List.for_all (function
    | (l, HRecd rt) -> wfLoc typeEnv l && wfRecdType typeEnv rt
    | (l, HMu mu)   -> wfLoc typeEnv l && wfMuType typeEnv mu
  )

and wfRely : TypeEnv.t -> rely -> bool =
fun typeEnv ->
  RelySet.for_all (fun (x,t) ->
    wfTyp typeEnv t
    (* NOTE: allowing variables not yet defined to be mentioned,
             so that don't need to lift var decls...
    match TypeEnv.lookupType x typeEnv with
      | Some StrongRef -> wfTyp typeEnv t
      | _              -> false
    *)
  )

let wfMuAbbrev : TypeEnv.t -> (ty_var list * mu_type) -> bool =
fun typeEnv (xs, mu) ->
  if List.length xs <> 0 then failwith "wfMuAbbrev type vars nyi";
  wfMuType typeEnv mu

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
                  | Some HEProxy _ -> failwith "subAndPack proxy"
                  | Some HERecd _ -> None
                  | Some HEMu mu ->
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

(* DEPRECATED *)
let heapSat : HeapEnv.t -> heap -> bool =
fun heapEnv heap ->
  List.for_all (fun (l,hb) ->
    match HeapEnv.lookupLoc l heapEnv, hb with
      (* TODO more permissive test? *)
      | Some HERecd rt1, HRecd rt2 -> rt1 = rt2
      | Some HEMu mu1,   HMu mu2   -> mu1 = mu2
      | _                          -> false
  ) heap

let removeHeap : HeapEnv.t -> heap -> HeapEnv.t =
  List.fold_left (fun acc (l,_) -> HeapEnv.removeLoc l acc)

let addHeap : HeapEnv.t -> heap -> HeapEnv.t =
  List.fold_left (fun acc (l,hb) ->
    if HeapEnv.memLoc l acc
    then failwith (spr "addHeap: %s already in heap env" (strLoc l))
    else HeapEnv.addLoc l (liftHeapBinding hb) acc)

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

(*
let joinHeapEnvs : HeapEnv.t -> HeapEnv.t -> HeapEnv.t option =
  let joinVars vars1 vars2 =
    VarMap.fold (fun x pt2 acc ->
      if not (VarMap.mem x vars2) then acc
      else let pt3 = VarMap.find x vars2 in
           let (t2,t3) = (projTyp pt2, projTyp pt3) in
           VarMap.add x (Typ (join t2 t3)) acc
    ) vars1 VarMap.empty
  in
  let joinLocs locs1 locs2 =
    LocMap.fold (fun l x acc ->
      match acc, LocMap.mem l locs2 with
        | Some locs, true ->
            begin match x, LocMap.find l locs2 with
              | HERecd rt1, HERecd rt2 ->
                  Some (LocMap.add l (HERecd (joinRecdTypes rt1 rt2)) locs)
              | x, y when x = y ->
                  Some (LocMap.add l x locs)
              | x, y ->
                  None
            end
        | _ -> None
    ) locs1 (Some LocMap.empty)
  in
  fun he1 he2 ->
    match joinLocs he1.locs he2.locs with
      | None -> None
      | Some locs ->
          let vars = joinVars he1.vars he2.vars in
          Some { vars = vars; locs = locs; }
*)

let joinHeapEnvs : HeapEnv.t -> HeapEnv.t -> HeapEnv.t option =

  let joinVars (he1, he2) =
    
    let maybeAddProxyLoc x maybePtr l1 l2 heAcc he1 he2 =
      match HeapEnv.lookupLoc l1 he1, HeapEnv.lookupLoc l2 he2 with
        (* add more flexible check? *)
        | Some heb, Some heb' when heb = heb' ->
            (* using fresh location const instead of existential location *)
            let l12   = LConst (genLocConst ()) in
            let t     = TRefLoc l12 in
            let t     = if maybePtr then Typ (TMaybe t) else (Typ t) in
            let heAcc = HeapEnv.addVar x t heAcc in
            let heAcc = HeapEnv.addLoc l12 heb heAcc in
            let heAcc = HeapEnv.addLoc l1 (HEProxy l12) heAcc in
            let heAcc = HeapEnv.addLoc l2 (HEProxy l12) heAcc in
            let he1   = HeapEnv.removeLoc l1 he1 in
            let he2   = HeapEnv.removeLoc l2 he2 in
            Some (heAcc, he1, he2)
        | Some heb, Some heb' ->
            let _ = pr "bad heapenvbind %s\n%s\n%s\n" x
              (strHeapEnvBinding (l1,heb)) (strHeapEnvBinding (l2,heb')) in
            None
        | _ ->
            let _ = pr "bad heapenvbind" in
            None
    in

    let initAcc = Some (HeapEnv.empty, he1, he2) in

    VarMap.fold (fun x pt1 acc ->
      ifSome acc begin fun (heAcc, he1, he2) ->
        if not (VarMap.mem x he2.vars) then acc
        else begin
          let pt2 = VarMap.find x he2.vars in
          let (t1,t2) = (projTyp pt1, projTyp pt2) in
          match t1, t2 with
            | TRefLoc l1, TRefLoc l2 when l1 <> l2 ->
                maybeAddProxyLoc x false l1 l2 heAcc he1 he2
            | TMaybe TRefLoc l1, TRefLoc l2
            | TRefLoc l1,        TMaybe TRefLoc l2
            | TMaybe TRefLoc l1, TMaybe TRefLoc l2 when l1 <> l2 ->
                maybeAddProxyLoc x true l1 l2 heAcc he1 he2
            | _ ->
                let heAcc = HeapEnv.addVar x (Typ (join t1 t2)) heAcc in
                Some (heAcc, he1, he2)
        end
      end
    ) he1.vars initAcc in

  let joinLocs (heAcc, he1, he2) =
    LocMap.fold (fun l x acc ->
      ifSome acc begin fun heAcc ->
        if not (LocMap.mem l he2.locs) then acc
        else begin
          match x, LocMap.find l he2.locs with
            | HERecd rt1, HERecd rt2 ->
                Some (HeapEnv.addLoc l (HERecd (joinRecdTypes rt1 rt2)) heAcc)
            | x, y when x = y ->
                Some (HeapEnv.addLoc l x heAcc)
            | x, y ->
                None
        end
      end
    ) he1.locs (Some heAcc) in

  fun he1 he2 ->
    match joinVars (he1, he2) with
      | None       -> None
      | Some stuff -> joinLocs stuff

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
  ) heapEnv.vars None

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
  simpleMapTyp (function TRefLoc _ -> TAny | s -> s) t

let unrollMuDef : mu_type -> (var * recd_type) -> recd_type =
fun mu -> function
  | "_", rt -> rt
  | x, TRecd(width,fts) ->
      let fMu = function MuVar y when x = y -> mu | someMu -> someMu in
      let mappers = { emptyMappers with fMu = fMu } in
      let fts = List.map (fun (f, t) -> (f, mapTyp mappers t)) fts in
      TRecd (width, fts)

let unrollMu : TypeEnv.t -> mu_type -> recd_type =
fun typeEnv mu ->
  match mu with
    | Mu(x,rt) -> unrollMuDef mu (x,rt)
    | MuAbbrev(t,[]) ->
        (match TypeEnv.lookupMuAbbrev t typeEnv with
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
    (fun heapEnv -> Some (HeapEnv.addLoc l (HEMu mu) heapEnv))
    (* recdSubAndPack removed witnesses, so now just fold the top loc *)

let eagerUnpack : recd_type -> (loc_var list * recd_type) =
fun (TRecd(width,fts)) ->
  let existentialLocs = ref [] in
  let foo = function
    | TExistsRef(l,mu) ->
        let l = genLocVar ~name:"unpack" () in
        let _ = existentialLocs := l :: !existentialLocs in
        TRefLoc (LVar l)
    | t -> t
  in
  let fts = List.map (fun (f,t) -> (f, simpleMapTyp foo t)) fts in
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
  let rec foo = function
    | TAny          
    | TBase TNum      -> Some (eInt 0)
    | TBase TStr      -> Some (eStr "")
    | TBase TBool     -> Some (eBool true)
    | TBase TUndef    -> Some eUndef
    | TBase TNull     -> Some eNull
    | TMaybe _        -> Some eNull
    | TArrow ((_, ts, _), ([], t, [])) ->
        (match foo t with
           | Some e -> Some (eFun (List.map (fun _ -> genSym ()) ts) (sExp e))
           | None   -> None)
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

let synthesizable : TypeEnv.t -> heap_binding -> bool =
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
                 let hb = List.assoc (LVar lv) hExpected in
                 if not (synthesizable typeEnv hb) then None
                 else
                   let lv = genLocVar ~name:"dummy" () in
                   let heb = liftHeapBinding hb in
                   let heapEnv = HeapEnv.addLoc (LVar lv) heb heapEnv in
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

(* TODO avoid capture *)
let applySubst : loc_subst -> typ -> typ =
fun subst ->
  simpleMapTyp (function
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
  (* let freshenOne x = genLocVar ~name:x () in *)
  let freshenOne x = genLocVar () in
  let ys = List.map freshenOne xs in
  List.combine xs (List.map (fun y -> LVar y) ys)

let strLocSubst : loc_subst -> string =
fun subst ->
  String.concat "\n"
    (List.map (fun (lvar,loc) -> spr "%s := %s" lvar (strLoc loc)) subst)

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

let strPathList : path_list -> string =
fun l ->
  commas (List.map (fun (fs,mu) -> spr "[%s] %s" (commas fs) (strMu mu)) l)

let strRootedPathList : rooted_path_list -> string =
fun (loc, mu, l) ->
  spr "(%s, %s, %s)" (strLoc loc) (strMu mu) (strPathList l)

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
                  | Some HEProxy _ -> failwith "subAndFold proxy"
                  | Some HERecd rt1 ->
                      let res = recdSubAndFold typeEnv heapEnv path rt1 rt2 in
                      resultAppend res (YesIf [(path, muExists)])
                  | Some HEMu mu ->
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
  List.fold_left (fun acc (l,hb) ->
    let rec checkLoc l =
      match HeapEnv.lookupLoc l heapEnv, hb, !Settings.castInsertionMode with
        (* TODO more permissive tests?
        | Some HERecd rt1, HRecd rt2, _ when rt1 = rt2 -> acc
        *)
        | Some HERecd rt1, HRecd rt2, _ when recdSub rt1 rt2 -> acc
        | Some HEMu mu1,   HMu mu2, _   when mu1 = mu2 -> acc
        | Some HERecd rt1, HMu mu, true ->
            let root = [] in
            let rt2 = unrollMu typeEnv mu in
            (match recdSubAndFold typeEnv heapEnv root rt1 rt2 with
              | YesIf pathList  -> resultAdd acc (l, mu, pathList)
              | Yes             -> resultAdd acc (l, mu, [])
              | No              -> No)
        | Some HEProxy l', _, _ -> checkLoc l' (* TODO need to remove anything once l' is used? *)
        | _                     -> No
    in
    checkLoc l
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
(*
        | None, TRefLoc l, None ->
            (* TODO currently handling only case where don't need any folds
               inside the object literal *)
            (match e.exp, pathLists with
               | EObj _, [] -> Some [eFold muRoot e]
               | _ -> None)
*)
        | _ -> None
    ) None ets in

  let foldFromEnv (locRoot, muRoot, pathLists) : exp list option =
    let rec tryPath path = function
      | TRefLoc l when l = locRoot ->
          Some (makeFolds path locRoot muRoot pathLists)
      | TRefLoc l ->
          (match HeapEnv.lookupLoc l heapEnv with
            | Some HERecd TRecd (_, fts) ->
                List.fold_left (fun acc (f,t) ->
                  ifNone acc (fun () -> tryPath (addPath path [f]) t)
                ) None fts
            | _ -> None)
      | _ -> None
    in
    VarMap.fold (fun x y acc ->
      ifNone acc begin fun () ->
        match y with
          | Val t | InvariantRef t -> tryPath (LvalVar x) t
          | StrongRef ->
              (match HeapEnv.lookupVar x heapEnv with
                 | Some Typ t -> tryPath (LvalVar x) t
                 | _ -> None)
      end
    ) typeEnv.bindings None in

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

let inlineUnfold mu e = match e.exp with
  | EVarRead x ->
      eTcInsert
        (eLet "_" (eUnfold mu (eVar x))
        (eVar x))
  | _ ->
      let xObj = genSym () in
      eTcInsert
        (eLet xObj e
        (eLet "_" (eUnfold mu (eVar xObj))
        (eVar xObj)))

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
           | Some (canLiftAll, folds) ->
               let canLiftAll = false in (* TODO *)
               YesIf (canLiftAll, folds))

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
let sTcErr s stmt  = sSeq [sExp (eTcErr s (eStr "XXX")); stmt]
let errS s stmt    = Err (sTcErr s stmt)

(* stuff synthesized information inside the rewritten exp/stmt: *)

let expWithInfo e pt       = { e with pt_e = pt }
let stmtWithInfo s pt he   = { s with pt_s = pt; he_s = he }
let okE e pt he out        = Ok (expWithInfo e pt, (pt, he, out))
let okS s pt he out        = Ok (stmtWithInfo s pt he, (pt, he, out))

let uncurry3 f (x,y,z)     = f x y z
let okE_ e                 = uncurry3 (okE e)
let okS_ s                 = uncurry3 (okS s)

let expWithExtraInfo e str  = { e with extra_info_e = str }
let stmtWithExtraInfo s str = { s with extra_info_s = str }

(* TODO *)
let compatible s t = match s, t with
  | TAny, _ -> true
  | TRefLoc(l1), TRefLoc(l2) -> l1 = l2
  | _, TRefLoc _ | TRefLoc _, _ -> false
  | TArrow _, TBase _ -> false
  | TBase x, TBase y when x <> y -> false
  | TUnion ts, _ when List.mem t ts -> true
  | _ -> false
  (* | _ -> true *)

let coerce (e, s, t) =
  let (s1,s2) = (strTyp s, strTyp t) in
  if sub s t then
    (* not wrapping with t here, so that AcePrinter can display the
       source type before any subsumption *)
    Ok (expWithInfo e (Typ s), false)
  else if not !Settings.castInsertionMode then
    Err (eTcErr (spr "not a subtype:\n%s\n%s" s1 s2) e)
  else if compatible s t then
    Ok (expWithInfo (eApp (eCast s t) [e]) (Typ t), true)
    (* requiring that the _calling context_ wrap with eTcInsert, in order to
       avoid double wrapping in the case where the inserted cast gets hoisted
       out into an assignment statement. *)
    (* Ok (expWithInfo (eApp (eTcInsert (eCast s t)) [e]) (Typ t), true) *)
  else
    Err (eTcErr (spr "not compatible:\n%s\n%s" s1 s2) e)

let rec tcExp (typeEnv, heapEnv, exp) = match exp.exp with

  | EBase(VNum _)  -> okE exp (Typ tNum)   heapEnv MoreOut.empty
  | EBase(VBool _) -> okE exp (Typ tBool)  heapEnv MoreOut.empty
  | EBase(VStr _)  -> okE exp (Typ tStr)   heapEnv MoreOut.empty
  | EBase(VUndef)  -> okE exp (Typ tUndef) heapEnv MoreOut.empty
  | EBase(VNull)   -> okE exp (Typ tNull)  heapEnv MoreOut.empty

  | EVarRead(x) ->
      (match TypeEnv.lookupType x typeEnv with
        | None -> errE (spr "var [%s] isn't defined" x) exp
        | Some(Val(t))
        | Some(InvariantRef(t)) ->
            okE exp (Typ t) heapEnv (MoreOut.addUsedVar x MoreOut.empty)
        | Some(StrongRef) ->
            (match HeapEnv.lookupVar x heapEnv with
              | None -> errE (spr "var [%s] is not in heap env" x) exp
              | Some(pt) ->
                  okE exp pt heapEnv (MoreOut.addUsedVar x MoreOut.empty)))

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
      okE exp (Typ (TArrow arrow)) heapEnv MoreOut.empty

  | EApp(eFun,eArgs) ->
      run tcExp (typeEnv, heapEnv, eFun)
        (fun eFun -> Err (eApp eFun eArgs))
        (fun eFun (ptFun,heapEnv,outFun) ->
           let (locs,ptFun) = stripExists ptFun in
           let finish = function
             | Ok (e, (pt, he, o)) -> Ok (e, (addExists locs pt, he, o))
             | err                 -> err
           in
           match ptFun with
            | Exists _ -> assert false
                (* Err (eApp (eTcErr "function has existential type" eFun) eArgs) *)
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
                finish (tcApp1 typeEnv heapEnv outFun eFun eArgs tArgs tRet)
            | Typ(TArrow(arrow)) ->
                finish (tcAppPoly typeEnv heapEnv outFun eFun eArgs arrow)
            | Typ(tFun) ->
                finish (tcApp2 typeEnv heapEnv outFun eFun eArgs tFun))

  | EObj(fes) ->
      tcObjLit typeEnv heapEnv (genLocVar ()) fes

  | EObjRead(e1,e2) ->
      let (e1Orig,e2Orig,heapEnvOrig) = (e1, e2, heapEnv) in
      runTcExp2 (typeEnv, heapEnv) (e1, e2)
        (fun (e1,e2) -> Err (eGet e1 e2))
        (fun (e1,e2) (pt1,_,heapEnv,out) ->
           let (locs1,pt1) = stripExists pt1 in
           let finish = addExists locs1 in
           match pt1, isStr e2 with
            | Typ(TRefLoc(l)), Some(f) ->
                (match HeapEnv.lookupLoc l heapEnv with
                  | None -> Err (eGet (eTcErr "not in heap" e1) e2)
                  | Some HEProxy _ -> Err (eGet (eTcErr "proxied" e1) e2)
                  | Some HERecd rt ->
                      (match findInRecdType f rt with
                        | Bound(tf) ->
                            okE (eGet e1 e2) (finish (Typ tf)) heapEnv out
                        | NotBound ->
                            if !Settings.strictObjGet
                            then Err (eTcErr "field not found" (eGet e1 e2))
                            else okE (eGet e1 e2) (finish (Typ tUndef)) heapEnv out
                        | MaybeBound ->
                            if !Settings.strictObjGet
                            then Err (eTcErr "field not found" (eGet e1 e2))
                            else okE (eGet e1 e2) (finish (Typ TAny)) heapEnv out)
                  | Some HEMu MuVar _ ->
                      failwith "tc EObjRead: mu var wasn't unrolled?"
                  | Some HEMu mu ->
                      (* inline backtracking *)
                      let e1 = inlineUnfold mu e1Orig in
                      tcExp (typeEnv, heapEnvOrig, eGet e1 e2Orig))

                      (* TODO rather than inserting the unfold inline,
                         could try to identify situations when it
                         is preferable to hoist the unfold out

                      let err = spr "need to unfold: %s" (strMu mu) in
                      (match lvalOf e1 with
                        | Some(lv) ->
                            (* let sRetry = sAssignLval lv (eUnfold mu (eLval lv)) in *)
                            let sRetry = sExp (eUnfold mu (eLval lv)) in
                            Err (eGet (eTcErrRetry err e1 sRetry) e2)
                        | _ ->
                            Err (eGet (eTcErr err e1) e2)))
                      *)
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
           let finish = addExists locs in
           match pt with
            | Typ(TRefLoc(l)) ->
                (match HeapEnv.lookupLoc l heapEnv with
                  | None -> Err (eFold mu (eTcErr "not in heap" e))
                  | Some HEProxy _ -> Err (eFold mu (eTcErr "loc proxied" e))
                  | Some HEMu _ -> Err (eFold mu (eTcErr "not recd type" e))
                  | Some HERecd rt ->
                      (match pack typeEnv heapEnv l rt mu with
                        | Some(heapEnv) ->
                            (* TODO show before/after heaps side-by-side *)
                            let ann = AcePrinter.strHeapEnv heapEnv in
                            let eFold = expWithExtraInfo (eFold mu e) ann in
                            okE eFold (finish pt) heapEnv out
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
                  | Some HEProxy _ -> Err (eUnfold mu (eTcErr "loc proxied" e))
                  | Some HERecd _ -> Err (eUnfold mu (eTcErr "not mu-type" e))
                  | Some HEMu mu ->
                      let rt = unrollMu typeEnv mu in
                      let (existentialLocs,rt) = eagerUnpack rt in
                      let pt = addExists (locs @ existentialLocs) pt in
                      let heapEnv = HeapEnv.addLoc l (HERecd rt) heapEnv in
                      let heapEnv =
                        List.fold_left
                          (fun acc li -> HeapEnv.addLoc (LVar li) (HEMu mu) acc)
                          heapEnv existentialLocs
                      in
                      (* TODO show before/after heaps side-by-side *)
                      let ann = AcePrinter.strHeapEnv heapEnv in
                      let eUnfold = expWithExtraInfo (eUnfold mu e) ann in
                      okE eUnfold pt heapEnv out)
            | _ ->
                let err = spr "not a reference type:\n%s\n" (strPreTyp pt) in
                Err (eUnfold mu (eTcErr err e)))

  | ETcInsert(e) ->
      run tcExp (typeEnv, heapEnv, e)
        (fun e -> Err (eTcInsert e))
        (fun e stuff -> okE_ (eTcInsert e) stuff)

  | ELet(x,e1,e2) ->
      if x <> "_" && TypeEnv.memVar x typeEnv
      then Err (eLet x (eTcErr (spr "var [%s] is already scope" x) e1) e2)
      else
        run tcExp (typeEnv, heapEnv, e1)
          (fun e1 -> Err (eLet x e1 e2))
          (fun e1 (pt1,heapEnv,out1) ->
             let (locs1,pt1) = stripExists pt1 in
             let finish = addExists locs1 in
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
                       okE (eLet x e1 e2) (finish pt2) heapEnv out))

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
    ) heapEnv.vars (RelySet.empty, heapEnvFun) in

  run tcStmt (typeEnv, heapEnvFun, body)
    (fun body -> Err (eFun xs body))
    (fun body (ptBody,_,out) ->
       (* don't need locs, because no effects in function types (for now) *)
       (* TODO *)
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
            okE (eAs (eFun xs body) ptArrow) ptArrow heapEnv out)

(* simpler version of tcAnnotatedFunPoly for pure arrows *)
and tcAnnotatedFun typeEnv heapEnv xs body rely tArgs tRet =
  let origArrow = OpenArrow (rely, (([], tArgs, []), ([], tRet, []))) in
  if not (wfPreType typeEnv origArrow) then
    Err (eTcErr "arrow not well-formed" (eAs (eFun xs body) origArrow))
  else if List.length xs <> List.length tArgs
    then failwith "add handling for len(actuals) != len(formals)"
  else

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
       (* TODO *)
       let (_,ptBody) = stripExists ptBody in (* same as above *)
       match ptBody with
        | Exists _ -> assert false
        | OpenArrow _ ->
            let err = "function body has an open type" in
            Err (eAs (eFun xs (sTcErr err body)) origArrow)
        | Typ(tBody) ->
            let ptArrow = finishArrow rely (([], tArgs, []), ([], tRet, [])) in
            if sub tBody tRet then
              okE (eAs (eFun xs body) ptArrow) ptArrow heapEnv MoreOut.empty
            else
              let err = "fun has bad fall-thru type" in
              Err (eAs (eFun xs (sTcErr err body)) origArrow))

and tcAnnotatedPolyFun typeEnv heapEnv xs body rely arrow =
  let ((allLocs,tArgs,h1),(someLocs,tRet,h2)) = arrow in
  let ptArrow = finishArrow rely arrow in
  if not (wfPreType typeEnv ptArrow) then
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
      List.fold_left (fun acc (l,hb) ->
        if HeapEnv.memLoc l acc
        then failwith "tcAnnotatedPolyFun: loc already bound"
        else HeapEnv.addLoc l (liftHeapBinding hb) acc
      ) heapEnvFun h1
    in
    run tcStmt (typeEnv, heapEnvFun, body)
      (fun body -> Err (eAs (eFun xs body) ptArrow))
      (fun body (pt,heapEnvFunOut,_) ->
         (* TODO do anything with locs? *)
         let (locs,pt) = stripExists pt in
         match pt with
          | Typ TBot ->
               let stuff = (ptArrow, heapEnv, MoreOut.empty) in
               okE_ (eAs (eFun xs body) ptArrow) stuff
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
                    else
                      (* TODO this is too late to infer folds at fall-thru.
                         need to check expected world inside tcStmt body *)
                      (match heapSatWithFolds typeEnv heapEnvFunOut h2 [] with
                        | Yes -> 
                            let stuff = (ptArrow, heapEnv, MoreOut.empty) in
                            okE_ (eAs (eFun xs body) ptArrow) stuff
                        | YesIf _ ->
                            failwith "tcAnnotatedPolyFun YesIf"
                        | No ->
                            let err =
                              spr "Bad fall-thru heap environment:\n\n%s\n\n \
                                   Expected heap:\n\n%s\n\n"
                              (AcePrinter.strHeapEnv heapEnvFunOut) (strHeap h2)
                            in
                            Err (eAs (eFun xs (sTcErr err body)) ptArrow)))
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
           run tcAndCoerce (typeEnv, heapEnv, eArg, tArg)
             (fun eArg -> (eArgs @ [eArg], None))
             (fun eArg (heapEnv,out') ->
                let out = MoreOut.combine out out' in
                (eArgs @ [eArg], Some (heapEnv, out)))
    ) ([], Some (heapEnv, outFun)) obligations
  in
  (match maybeOutput with
    | None -> Err (eApp eFun eArgs)
    | Some(heapEnv,out) ->
        okE (eApp eFun eArgs) (Typ tRet) heapEnv out)

and tcAppPoly typeEnv heapEnv outFun eFun eArgs arrow =
  let heapEnvOrig = heapEnv in
  let eArgsOrig = eArgs in
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
   | Some(tArgsActual,existentialLocs,heapEnv,out) -> begin
       let substAndHeapEnv =
         computeLocSubst typeEnv heapEnv allLocs tArgsActual tArgsExpected h1 in
       match substAndHeapEnv with
        | None -> Err (eTcErr "couldn't infer instantiations" (eApp eFun eArgs))
        | Some (subst, heapEnv) ->
            let locActuals = List.map snd subst in
            if locActuals <> Utils.removeDupes locActuals then
              Err (eTcErr
                (spr "inferred loc instantations contains a duplicate:\n\n%s"
                   (strLocSubst subst)) (eApp eFun eArgs))
            else
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
            else begin
              let ets = List.combine eArgs tArgsExpected in
              match heapSatWithFolds typeEnv heapEnv h1 ets with
                | No ->
                    let err = "input heap not satisfied" in
                    Err (eTcErr err (eApp eFun eArgs))
                | Yes ->
                    let substFresh = freshen someLocs in
                    let tRet = applySubst (subst @ substFresh) tRet in 
                    let h2 = applySubstToHeap (subst @ substFresh) h2 in
                    let heapEnv = removeHeap heapEnv h1 in
                    let heapEnv = addHeap heapEnv h2 in
                    let ptRet = addExists existentialLocs (Typ tRet) in
                    let ann =
                      if List.length subst = 0 then ""
                      else spr "inferred location instantiations:\n\n%s" 
                             (strLocSubst subst) in
                    let eApp = expWithExtraInfo (eApp eFun eArgs) ann in
                    okE eApp ptRet heapEnv out
                | YesIf (_, folds) ->
                    let heapEnv = heapEnvOrig in
                    let eArgs =
                      match List.rev eArgsOrig with
                       | [] -> failwith "app yesif"
                       | eLast::eRest ->
                           let eLast = inlineExpForFolds folds eLast in
                           List.rev (eLast :: eRest)
                    in
                    (* inline backtracking *)
                    (match tcAppPoly typeEnv heapEnv outFun eFun eArgs arrow with
                      | Ok (e, stuff) -> okE_ e stuff
                      | Err _ ->
                          let err = "input heap not sat even with folds" in
                          Err (eTcErr err (eApp eFun eArgsOrig)))
            end
     end

and tcApp2 typeEnv heapEnv outFun eFun eArgs tFun =
  let tAnys = List.map (function _ -> TAny) eArgs in
  run coerce (eFun, tFun, pureArrow tAnys TAny)
    (fun eFun -> Err (eApp eFun eArgs))
    (fun eFun insertedCast ->
       let eFun = if insertedCast then eTcInsert eFun else eFun in
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
             okE (eApp eFun eArgs) (Typ TAny) heapEnv out))

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
        let heapEnv = HeapEnv.addLoc (LVar locObj) (HERecd tRecd) heapEnv in
        okE obj ptPtr heapEnv out
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
        (fun e (_,heapEnv,out) -> okS (sExp e) (Typ tUndef) heapEnv out)

  | SReturn(e) ->
      (* not just calling tcAndCoerce, because want to add synthesized
         return type to output *)
      let heapEnvOrig = heapEnv in
      let eOrig = e in
      run tcExp (typeEnv, heapEnv, e)
        (fun e -> Err (sRet e))
        (fun e (pt,heapEnv,out) ->
           let (locs,pt) = stripExists pt in
           let finish = addExists locs in
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
                      let ann =
                        if List.length subst = 0 then ""
                        else spr "inferred location instantiations:\n\n%s" 
                               (strLocSubst subst) in
                      let tGoal = applySubst subst tGoal in
                      let hGoal = applySubstToHeap subst hGoal in
                      run tcCoerce (true, typeEnv, heapEnv, e, t, tGoal)
                        (fun e -> Err (stmtWithExtraInfo (sRet e) ann))
                        (fun e (heapEnv,out') ->
                           let ets = [(e,t)] in
                           match heapSatWithFolds typeEnv heapEnv hGoal ets with
                             | No ->
                                 let err =
                                   spr "%s:\n\n%s\n\n%s:\n\n%s"
                                     "Expected heap"
                                     (strHeap hGoal)
                                     "Not satisfied by current heap environment"
                                     (AcePrinter.strHeapEnv heapEnv)
                                 in
                                 Err (stmtWithExtraInfo (sRet (eTcErr err e)) ann)
                             (*
                             | YesIf (true, folds) ->
                                 let sRetry = retryStmtForFolds folds in
                                 Err (sRet (eTcErrRetry err e sRetry))
                             | YesIf (false, folds) ->
                             *)
                             | YesIf (_, folds) ->
                                 (* inline backtracking *)
                                 let e' = inlineExpForFolds folds eOrig in
                                 run tcStmt (typeEnv, heapEnvOrig, sRet e')
                                   (fun _ ->
                                      let err =
                                        spr "%s,\n%s"
                                          "expected heap not satisfied"
                                          "even after inlining folds and backtracking"
                                      in
                                      Err (stmtWithExtraInfo (sRet (eTcErr err e)) ann))
                                   (fun s stuff -> okS_ s stuff)
                             | Yes ->
                                 let out = MoreOut.combine out out' in
                                 let out = MoreOut.addRetType t out in
                                 let sRet = stmtWithExtraInfo (sRet e) ann in
                                 okS sRet (finish (Typ TBot)) heapEnv out)))

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
             let finish = addExists (locs @ [locObj]) in
             let typeEnv = TypeEnv.addLocVars locs typeEnv in
             let typeEnv = TypeEnv.addLocVar locObj typeEnv in
             let typeEnv = TypeEnv.addVar x StrongRef typeEnv in
             let heapEnv = HeapEnv.addVar x ptObj heapEnv in
             let sObj = stmtWithInfo (sAssign x obj) (Typ tUndef) heapEnv in
             run tcStmt (typeEnv, heapEnv, s)
               (fun s -> Err (sLetRef x (sSeq [sAssign x obj; s])))
               (fun s (pt,heapEnv,out) ->
                  let heapEnv = HeapEnv.removeVar x heapEnv in
                  okS (sLetRef x (sSeq [sObj; s])) (finish pt) heapEnv out)
      end

  | SVarDecl(x,s) ->
      if TypeEnv.memVar x typeEnv
      then errS (spr "var [%s] is already scope" x) stmt
      else
        let typeEnv = TypeEnv.addVar x StrongRef typeEnv in
        let heapEnv = HeapEnv.addVar x (Typ tUndef) heapEnv in
        run tcStmt (typeEnv, heapEnv, s)
          (fun s -> Err (wrapStmt (SVarDecl (x, s))))
          (fun s (pt,heapEnv,out) ->
             let heapEnv = HeapEnv.removeVar x heapEnv in
             okS (sLetRef x s) pt heapEnv out)

  | SVarAssign(x,e) ->
      begin match TypeEnv.lookupType x typeEnv with
        | None -> errS (spr "var [%s] isn't defined" x) stmt
        | Some(Val _) -> errS (spr "val [%s] is not assignable" x) stmt
        | Some(InvariantRef(t)) ->
            run tcAndCoerce (typeEnv, heapEnv, e, t)
              (fun e -> Err (sAssign x e))
              (fun e (heapEnv,out) -> okS (sAssign x e) (Typ t) heapEnv out)
        | Some(StrongRef) ->
            run tcExp (typeEnv, heapEnv, e)
              (fun e -> Err (sAssign x e))
              (fun e (pt,heapEnv,out) ->
                 let (locs,pt) = stripExists pt in
                 let finish = addExists locs in
                 let heapEnv = HeapEnv.addVar x pt heapEnv in
                 okS (sAssign x e) (finish (Typ tUndef)) heapEnv out)
                 (* okS (sAssign x e) (addExists locs pt) heapEnv out) *)
                 (* TODO don't want to confuse last expression with completion,
                    so if need to chain assignments, need additional info... *)
      end

  | SSeq(s1,s2) ->
      (* calling __tcStmt to avoid backtracking, since want failures to
         propagate to the caller of tcStmt on the entire sequence statement *)
      run __tcStmt (typeEnv, heapEnv, s1)
        (fun s1 -> Err (sSeq [s1; s2]))
        (fun s1 (pt1,heapEnv1,out1) ->
           let (locs1,pt1') = stripExists pt1 in
           let finish = addExists locs1 in
           match pt1' with
            | Typ(TBot) -> okS (sSeq [s1; s2]) pt1 heapEnv1 out1
            | _ ->
                let typeEnv = TypeEnv.addLocVars locs1 typeEnv in
                run tcStmt (typeEnv, heapEnv1, s2)
                  (fun s2 -> Err (sSeq [s1; s2]))
                  (fun s2 (pt2,heapEnv2,out2) ->
                     let out = MoreOut.combine out1 out2 in
                     okS (sSeq [s1; s2]) (finish pt2) heapEnv2 out))

  | SIf(e1,s2,s3) ->
      (* requiring boolean guard for now *)
      run tcAndCoerceLocally (typeEnv, heapEnv, e1, tBool)
        (fun e1 -> Err (sIf e1 s2 s3))
        (fun e1 (heapEnv,out1) -> run tcStmt (typeEnv, heapEnv, s2)
           (fun s2 -> Err (sIf e1 s2 s3))
           (fun s2 (ptThen,heapEnv2,out2) -> run tcStmt (typeEnv, heapEnv, s3)
              (fun s3 -> Err (sIf e1 s2 s3))
              (fun s3 (ptElse,heapEnv3,out3) ->
                 (* TODO need locs? *)
                 let ptThen = snd (stripExists ptThen) in
                 let ptElse = snd (stripExists ptElse) in
                 let (tThen,tElse) = (projTyp ptThen, projTyp ptElse) in
                 let finish heFinal =
                   let out = List.fold_left MoreOut.combine out1 [out2; out3] in
                   okS (sIf e1 s2 s3) (Typ (join tThen tElse)) heFinal out
                 in
                 match tThen, tElse, joinHeapEnvs heapEnv2 heapEnv3 with
                  | TBot, TBot, _       -> finish HeapEnv.empty
                  | _   , TBot, _       -> finish heapEnv2
                  | TBot, _   , _       -> finish heapEnv3
                  | _   , _   , Some he -> finish he
                  | _   , _   , None    ->
                      let err = spr "can't join heap env locs\n%s\n%s\n"
                                  (HeapEnv.strLocs heapEnv2)
                                  (HeapEnv.strLocs heapEnv3) in
                      Err (sTcErr err (sIf e1 s2 s3)))))

  | SWhile(e,s) ->
      run tcAndCoerceLocally (typeEnv, heapEnv, e, tBool)
        (fun e -> Err (sWhile e s))
        (fun e (heapEnv1,out1) ->
           (*
           if not (HeapEnv.equal heapEnv heapEnv1)
           then Err (sWhile e (sTcErr "heapEnv1 != heapEnv" s))
           else
           *)
             run tcStmt (typeEnv, heapEnv1, s)
               (fun s -> Err (sWhile e s))
               (fun s (_,heapEnv2,out2) ->
                  match joinHeapEnvs heapEnv heapEnv2 with
                   | None ->
                       let err =
                          spr "couldn't join heapEnv and heapEnv2\n\n%s\n%s"
                          (HeapEnv.strLocs heapEnv) (HeapEnv.strLocs heapEnv2)
                       in
                       Err (sWhile e (sSeq [s; sExp (eTcErr err (eStr "XXX"))]))
                   | Some heJoin ->
                       let out = MoreOut.combine out1 out2 in
                       okS (sWhile e s) (Typ tUndef) heJoin out))

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
                (fun s stuff ->
                   let ann =
                     spr "before   %s: ref / *%s: %s\nafter    %s: ref(%s)"
                       x x (strTyp tCurrentX) x (strTyp tGoalX) in
                   let sInvar = stmtWithExtraInfo (sInvar x tGoalX s) ann in
                   okS_ sInvar stuff))

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
        let (s1,s2) = (strRelySet rely, strRelySet guarantee) in
        let err = spr "Rely != Guarantee\n\n%s\n\n%s" s1 s2 in
        Err (sClose xs (sTcErr err s))
      else
        let annFrozen = "Converted to invariant references:" in
        let dashes = String.make (String.length annFrozen) '-' in
        let annFrozen = spr "\n%s\n%s\n%s\n" dashes annFrozen dashes in
        let (typeEnv,heapEnv,annFrozen) =
          RelySet.fold (fun (x,t) (acc1,acc2,acc3) ->
            let acc1 = TypeEnv.addVar x (Val t) acc1 in
            let acc2 = HeapEnv.removeVar x acc2 in
            let acc3 = spr "%s\n%s : ref (%s)" acc3 x (strTyp t) in
            (acc1, acc2, acc3)
          ) rely (typeEnv, heapEnv, annFrozen)
        in
        run tcStmt (typeEnv, heapEnv, s)
          (fun s -> Err (sClose xs s))
          (fun s stuff ->
             let ann = spr "%s\n%s" (AcePrinter.strHeapEnv heapEnv) annFrozen in
             let sClose = stmtWithExtraInfo (sClose xs s) ann in
             okS_ sClose stuff)

  | SObjAssign(e1,e2,e3) ->
      let (e1Orig,e2Orig,e3Orig,heapEnvOrig) = (e1, e2, e3, heapEnv) in
      runTcExp3 (typeEnv, heapEnv) (e1, e2, e3)
        (fun (e1,e2,e3) -> Err (sSet e1 e2 e3))
        (fun (e1,e2,e3) (pt1,_,pt3,heapEnv,out) ->
           let (locs1,pt1) = stripExists pt1 in
           let (locs3,pt3) = stripExists pt3 in
           let finish = addExists (locs1 @ locs3) in
           match pt1, isStr e2, pt3 with
            | Exists _, _, _ -> assert false
            | Typ(TRefLoc(l)), Some(f), Typ(t3) ->
                (match HeapEnv.lookupLoc l heapEnv with
                  | None -> Err (sSet (eTcErr "not in heap" e1) e2 e3)
                  | Some HEProxy _ -> Err (sSet (eTcErr "proxied" e1) e2 e3)
                  | Some HERecd rt ->
                      let rt' = TRecd (ExactDomain, [(f,t3)]) in
                      let rt = extendRecdType rt rt' in
                      let heapEnv = HeapEnv.addLoc l (HERecd rt) heapEnv in
                      (* same thing with chaining VarAssign
                      okS (sSet e1 e2 e3) (addExists locs3 (Typ t3)) heapEnv out *)
                      okS (sSet e1 e2 e3) (finish (Typ tUndef)) heapEnv out
                  | Some HEMu MuVar _ ->
                      failwith "tc EObjAssign: mu var wasn't expanded?"
                  | Some HEMu mu ->
                      (* inline backtracking *)
                      let e1 = inlineUnfold mu e1Orig in
                      tcStmt (typeEnv, heapEnvOrig, sSet e1 e2Orig e3Orig))
  
                      (* TODO same as for EObjRead, could hoist sometimes
                      let err = spr "need to unfold: %s" (strMu mu) in
                      (match lvalOf e1 with
                        | Some(lv) ->
                            let sRetry = sExp (eUnfold mu (eLval lv)) in
                            Err (sSet (eTcErrRetry err e1 sRetry) e2 e3)
                        | _ ->
                            Err (sSet (eTcErr err e1) e2 e3)))
                      *)
            | _, None, _ ->
                Err (sSet e1 (eTcErr "dynamic key" e2) e3)
            | _, _, OpenArrow _ ->
                Err (sSet e1 e2 (eTcErr "open function type" e3))
            | Typ t, _, _ ->
                let err = spr "not a ref type: %s" (strTyp t) in
                (match lvalOf e1, refCast t with
                  | Some lv, Some cast ->
                      let sRetry = sAssignLval lv (eApp cast [eLval lv]) in
                      Err (sSet (eTcErrRetry err e1 sRetry) e2 e3)
                  (* could add this case: | None, Some(cast) -> *)
                  | _ ->
                      Err (sSet (eTcErr err e1) e2 e3))
            | OpenArrow _, _, _ ->
                let err = spr "not strong object type: %s" (strPreTyp pt1) in
                Err (sSet (eTcErr err e1) e2 e3))

  | SLoadedSrc(f,s) ->
      run tcStmt (typeEnv, heapEnv, s)
        (fun s -> Err (wrapStmt (SLoadedSrc (f, s))))
        (fun s stuff -> okS_ (wrapStmt (SLoadedSrc (f, s))) stuff)

  | SExternVal(x,tx,s) ->
      let typeEnv = TypeEnv.addVar x (Val tx) typeEnv in
      run tcStmt (typeEnv, heapEnv, s)
        (fun s -> Err (wrapStmt (SExternVal (x, tx, s))))
        (fun s stuff -> okS_ (wrapStmt (SExternVal (x, tx, s))) stuff)

  | STcInsert(s) ->
      run tcStmt (typeEnv, heapEnv, s)
        (fun s -> Err (sTcInsert s))
        (fun s stuff -> okS_ (sTcInsert s) stuff)

  | SMuAbbrev(x,def,s) ->
      if not (wfMuAbbrev typeEnv def) then
        Err (sTcErr "mu abbreviation not well-formed" (sMuDef x def s))
      else
        let typeEnv = TypeEnv.addMuAbbrev x def typeEnv in
        run tcStmt (typeEnv, heapEnv, s)
          (fun s -> Err (sMuDef x def s))
          (fun s stuff -> okS_ (sMuDef x def s) stuff)

  | SBlankLine ->
      okS sBlankLine (Typ tUndef) heapEnv MoreOut.empty

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

and tcAndCoerce args          = _tcAndCoerce true args
and tcAndCoerceLocally args   = _tcAndCoerce false args

and _tcAndCoerce hoistCasts (typeEnv, heapEnv, e, tGoal) =
  run tcExp (typeEnv, heapEnv, e)
    (fun e -> Err e)
    (fun e (pt,heapEnv,out) ->
       let (_,pt) = stripExists pt in (* TODO okay to throw away locs? *)
       match pt with
        | Exists _ -> assert false
        | OpenArrow _ -> errE "cannot coerce from open arrow" e
        | Typ(t) ->
            run tcCoerce (hoistCasts, typeEnv, heapEnv, e, t, tGoal)
              (fun e -> Err e)
              (fun e (heapEnv,out') ->
                 let out = MoreOut.combine out out' in
                 Ok (e, (heapEnv, out))))

and tcCoerce (hoistCasts, typeEnv, heapEnv, e, t, tGoal) =
  run coerce (e, t, tGoal)
    (fun eErr -> Err eErr)
    (fun eOk insertedCast ->
       (* not calling okE to preserve source type stuffed by coerce *)
       if not insertedCast then
         Ok (eOk, (heapEnv, MoreOut.empty))
       else
         match hoistCasts, lvalOf e with
           | true, Some lv ->
               let sRetry = sAssignLval lv eOk in
               Err (eTcErrRetry "tcCoerce backtracking" e sRetry)
           | _ ->
               Ok (eTcInsert eOk, (heapEnv, MoreOut.empty)))
(*
       (* if coercion inserted, hoist it out to an assignment if
          possible rather than inserting the cast locally *)
       match insertedCast && hoistCasts, lvalOf e with
        | true, Some(lv) ->
            let sRetry = sAssignLval lv eOk in
            Err (eTcErrRetry "tcCoerce backtracking" e sRetry)
        | _ ->
            Ok (eOk, (heapEnv, MoreOut.empty)))
*)

let removeTcInserts prog =
  mapStmt (* keep in sync with what tc can insert *)
    (function
      (* | EApp({exp=ETcInsert{exp=ECast _}},[eArg]) -> eArg.exp *)
      | EApp({exp=ETcInsert{exp=ECast _}},[eArg]) ->
          failwith "removeTcInserts: cast should've been inserted differently"
      | ETcInsert({exp=EApp({exp=ECast _},[eArg])}) -> eArg.exp
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

