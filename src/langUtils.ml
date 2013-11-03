
open Lang

let wrapExp e      = { exp = e }
let eFun xs s      = wrapExp (EFun (xs, s))
let eStr s         = wrapExp (EBase (VStr s))
let eUndef         = wrapExp (EBase (VUndef))
let eVar x         = wrapExp (EVarRead x)
let eApp e es      = wrapExp (EApp (e, es))
let eAs e t        = wrapExp (EAs (e, t))
let eCast s t      = wrapExp (ECast (s, t))
let eTcErr s e     = wrapExp (ETcErr (s, e))
let eObj l         = wrapExp (EObj l)
let eGet e1 e2     = wrapExp (EObjRead (e1, e2))

let wrapStmt s     = { stmt = s }
let sRet e         = wrapStmt (SReturn e)
let sLetRef x s    = wrapStmt (SVarDecl (x, s))
let sAssign x e    = wrapStmt (SVarAssign (x, e))
let sInvar x t s   = wrapStmt (SVarInvariant (x, t, s))
let sClose xs s    = wrapStmt (SClose (xs, s))
let sIf e s1 s2    = wrapStmt (SIf (e, s1, s2))
let sWhile e s     = wrapStmt (SWhile (e, s))
let sLoaded f s    = wrapStmt (SLoadedSrc (f, s))
let sExp e         = wrapStmt (SExp e)
let sSet e1 e2 e3  = wrapStmt (SObjAssign (e1, e2, e3))
let sSkip          = sExp (eUndef)

let rec sSeq = function
  | []    -> failwith "eSeq: must call with at least one exp"
  | [s]   -> s
  | s::ss -> wrapStmt (SSeq (s, sSeq ss))

let sSeq_ ss = (sSeq ss).stmt

let tNum    = TBase TNum
let tStr    = TBase TStr
let tBool   = TBase TBool
let tUndef  = TBase TUndef
let tNull   = TBase TNull

let tUnion ts =
  let l = List.flatten (List.map (function TUnion(l) -> l | t -> [t]) ts) in
  TUnion (Utils.removeDupes l)

let ptArrow r tArgs tRet =
  if RelySet.is_empty r then Typ (TArrow (tArgs, tRet))
  else OpenArrow (r, tArgs, tRet)

let isStr = function
  | {exp=EBase(VStr(s))} -> Some s
  | _ -> None

let rec mapExp fE fS {exp=e} = {exp = mapExp_ fE fS e}

and mapStmt fE fS {stmt=s} = {stmt = mapStmt_ fE fS s}

and mapExp_ fE fS = function
  | EBase(v) -> fE (EBase v)
  | EVarRead(x) -> fE (EVarRead x)
  | EFun(xs,s) -> fE (EFun (xs, mapStmt fE fS s))
  | EApp(e,es) -> fE (EApp (mapExp fE fS e, List.map (mapExp fE fS) es))
  | EAs(e,t) -> fE (EAs (mapExp fE fS e, t))
  | ECast(s,t) -> fE (ECast (s, t))
  | ETcErr(s,e) -> fE (ETcErr (s, mapExp fE fS e))
  | EObj(l) -> fE (EObj (List.map (fun (f,e) -> (f, mapExp fE fS e)) l))
  | EObjRead(e1,e2) -> fE (EObjRead (mapExp fE fS e1, mapExp fE fS e2))

and mapStmt_ fE fS = function
  | SExp(e) -> fS (SExp (mapExp fE fS e))
  | SReturn(e) -> fS (SReturn (mapExp fE fS e))
  | SVarDecl(x,s) -> fS (SVarDecl (x, mapStmt fE fS s))
  | SVarAssign(x,e) -> fS (SVarAssign (x, mapExp fE fS e))
  | SSeq(s1,s2) -> fS (SSeq (mapStmt fE fS s1, mapStmt fE fS s2))
  | SIf(e,s1,s2) -> fS (SIf (mapExp fE fS e, mapStmt fE fS s1, mapStmt fE fS s2))
  | SWhile(e,s) -> fS (SWhile (mapExp fE fS e, mapStmt fE fS s))
  | SVarInvariant(x,t,s) -> fS (SVarInvariant (x, t, mapStmt fE fS s))
  | SClose(xs,s) -> fS (SClose (xs, mapStmt fE fS s))
  | SLoadedSrc(f,s) -> fS (SLoadedSrc (f, mapStmt fE fS s))
  | SExternVal(x,t,s) -> fS (SExternVal (x, t, mapStmt fE fS s))
  | SObjAssign(e1,e2,e3) ->
      fS (SObjAssign (mapExp fE fS e1, mapExp fE fS e2, mapExp fE fS e3))

(* [e; undefined] is inserted often by LamJS and ImpScript parsing *)
let removeUndefs stmt =
  mapStmt
    (fun x -> x)
    (function
       | SSeq ({stmt = s}, {stmt = SExp {exp = EBase VUndef}}) -> s
       | s -> s)
    stmt
