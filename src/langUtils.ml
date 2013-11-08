
open Lang

let wrapExp e      = { exp = e }
let eFun xs s      = wrapExp (EFun (xs, s))
let eStr s         = wrapExp (EBase (VStr s))
let eUndef         = wrapExp (EBase (VUndef))
let eVar x         = wrapExp (EVarRead x)
let eApp e es      = wrapExp (EApp (e, es))
let eAs e t        = wrapExp (EAs (e, t))
let eCast s t      = wrapExp (ECast (s, t))
let eObj l         = wrapExp (EObj l)
let eGet e1 e2     = wrapExp (EObjRead (e1, e2))
let eFold mu e     = wrapExp (EFold (mu, e))
let eUnfold mu e   = wrapExp (EUnfold (mu, e))
let eTcInsert e    = wrapExp (ETcInsert e)

let wrapStmt s     = { stmt = s }
let sRet e         = wrapStmt (SReturn e)
let sLetRef x s    = wrapStmt (SVarDecl (x, s))
let sAssign x e    = wrapStmt (SVarAssign (x, e))
let sInvar x t s   = wrapStmt (SVarInvariant (x, t, s))
let sClose xs s    = wrapStmt (SClose (xs, s))
let sIf e s1 s2    = wrapStmt (SIf (e, s1, s2))
let sWhile e s     = wrapStmt (SWhile (e, s))
let sLoaded f s    = wrapStmt (SLoadedSrc (f, s))
let sExtern x t s  = wrapStmt (SExternVal (x, t, s))
let sTyDef x y s   = wrapStmt (STyAbbrev (x, y, s))
let sExp e         = wrapStmt (SExp e)
let sSet e1 e2 e3  = wrapStmt (SObjAssign (e1, e2, e3))
let sTcInsert s    = wrapStmt (STcInsert s)
let sSkip          = sExp (eUndef)

let rec sSeq = function
  | []    -> failwith "eSeq: must call with at least one exp"
  | [s]   -> s
  | s::ss -> wrapStmt (SSeq (s, sSeq ss))

let sSeq_ ss = (sSeq ss).stmt

let eTcErr s e          = wrapExp (ETcErr (s, e, None))
let eTcErrRetry s e so  = wrapExp (ETcErr (s, e, Some so))

let tNum    = TBase TNum
let tStr    = TBase TStr
let tBool   = TBase TBool
let tUndef  = TBase TUndef
let tNull   = TBase TNull


let tUnion ts =
  let rec flatten = function
    | TUnion(ts) -> List.concat (List.map flatten ts)
    | t          -> [t]
  in
  TUnion (Utils.removeDupes (flatten (TUnion ts)))
    (* instead of just removeDupes, might want to look for
       equivalent types like reordered unions *)

let ptArrow r tArgs tRet =
  if RelySet.is_empty r then Typ (TArrow (tArgs, tRet))
  else OpenArrow (r, tArgs, tRet)

let isStr = function
  | {exp=EBase(VStr(s))} -> Some s
  | _ -> None

(* might want to include an fT parameter for these mappers *)

let rec mapExp fE fS {exp=e} = {exp = mapExp_ fE fS e}

and mapStmt fE fS {stmt=s} = {stmt = mapStmt_ fE fS s}

and mapExp_ fE fS = function
  | EBase(v) -> fE (EBase v)
  | EVarRead(x) -> fE (EVarRead x)
  | EFun(xs,s) -> fE (EFun (xs, mapStmt fE fS s))
  | EApp(e,es) -> fE (EApp (mapExp fE fS e, List.map (mapExp fE fS) es))
  | EAs(e,t) -> fE (EAs (mapExp fE fS e, t))
  | ECast(s,t) -> fE (ECast (s, t))
  | ETcErr(s,e,so) -> fE (ETcErr (s, mapExp fE fS e, so)) (* skipping so *)
  | ETcInsert(e) -> fE (ETcInsert (mapExp fE fS e))
  | EObj(l) -> fE (EObj (List.map (fun (f,e) -> (f, mapExp fE fS e)) l))
  | EObjRead(e1,e2) -> fE (EObjRead (mapExp fE fS e1, mapExp fE fS e2))
  | EFold(mu,e) -> fE (EFold (mu, mapExp fE fS e))
  | EUnfold(mu,e) -> fE (EUnfold (mu, mapExp fE fS e))

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
  | STcInsert(s) -> fS (STcInsert (mapStmt fE fS s))
  | STyAbbrev(x,def,s) -> fS (STyAbbrev (x, def, mapStmt fE fS s))
  | SObjAssign(e1,e2,e3) ->
      fS (SObjAssign (mapExp fE fS e1, mapExp fE fS e2, mapExp fE fS e3))

let rec mapTyp fT = function
  | TBase(bt) -> fT (TBase bt)
  | TArrow(ts,t) -> fT (TArrow (List.map (mapTyp fT) ts, mapTyp fT t))
  | TUnion(ts) -> fT (TUnion (List.map (mapTyp fT) ts))
  | TAny -> fT TAny
  | TBot -> fT TBot
  | TVar(x) -> fT (TVar x)
  | TMaybe(t) -> fT (TMaybe (mapTyp fT t))
  | TRefLoc(l) -> fT (TRefLoc l)
  | TRefMu(MuAbbrev(x,ys)) -> fT (TRefMu (MuAbbrev (x, ys)))
  | TRefMu(Mu(x,TRecd(width,fts))) ->
      let fts = List.map (fun (f,t) -> (f, mapTyp fT t)) fts in
      fT (TRefMu (Mu (x, TRecd (width, fts))))

let rec foldExp fE fS acc {exp=e} =
  foldExp_ fE fS acc e

and foldStmt fE fS acc {stmt=s} =
  foldStmt_ fE fS acc s

and foldExp_ fE fS acc = function
  | EBase(v) ->
      fE acc (EBase v)
  | EVarRead(x) ->
      fE acc (EVarRead x)
  | EFun(xs,s) ->
      let acc = foldStmt fE fS acc s in
      fE acc (EFun (xs, s))
  | EApp(e,es) ->
      let acc = List.fold_left (foldExp fE fS) acc (e::es) in
      fE acc (EApp (e, es))
  | EAs(e,t) ->
      let acc = foldExp fE fS acc e
      in fE acc (EAs (e, t))
  | ECast(s,t) ->
      fE acc (ECast (s, t))
  | ETcErr(s,e,so) ->
      let acc = foldExp fE fS acc e in
      fE acc (ETcErr (s, e, so)) (* skipping so *)
  | ETcInsert(e) ->
      let acc = foldExp fE fS acc e in
      fE acc (ETcInsert e)
  | EObj(l) ->
      let acc = List.fold_left (fun acc (_,e) -> foldExp fE fS acc e) acc l in
      fE acc (EObj l)
  | EObjRead(e1,e2) ->
      let acc = List.fold_left (foldExp fE fS) acc [e1;e2] in
      fE acc (EObjRead (e1, e2))
  | EFold(mu,e) ->
      let acc = foldExp fE fS acc e in
      fE acc (EFold (mu, e))
  | EUnfold(mu,e) ->
      let acc = foldExp fE fS acc e in
      fE acc (EUnfold (mu, e))

and foldStmt_ fE fS acc = function
  | SExp(e) ->
      let acc = foldExp fE fS acc e in
      fS acc (SExp e)
  | SReturn(e) ->
      let acc = foldExp fE fS acc e in
      fS acc (SReturn e)
  | SVarDecl(x,s) ->
      let acc = foldStmt fE fS acc s in
      fS acc (SVarDecl (x, s))
  | SVarAssign(x,e) ->
      let acc = foldExp fE fS acc e in
      fS acc (SVarAssign (x, e))
  | SSeq(s1,s2) ->
      let acc = List.fold_left (foldStmt fE fS) acc [s1;s2] in
      fS acc (SSeq (s1, s2))
  | SIf(e,s1,s2) ->
      let acc = foldExp fE fS acc e in
      let acc = List.fold_left (foldStmt fE fS) acc [s1;s2] in
      fS acc (SIf (e, s1, s2))
  | SWhile(e,s) ->
      let acc = foldExp fE fS acc e in
      let acc = foldStmt fE fS acc s in
      fS acc (SWhile (e, s))
  | SVarInvariant(x,t,s) ->
      let acc = foldStmt fE fS acc s in
      fS acc (SVarInvariant (x, t, s))
  | SClose(xs,s) ->
      let acc = foldStmt fE fS acc s in
      fS acc (SClose (xs, s))
  | SLoadedSrc(f,s) ->
      let acc = foldStmt fE fS acc s in
      fS acc (SLoadedSrc (f, s))
  | SExternVal(x,t,s) ->
      let acc = foldStmt fE fS acc s in
      fS acc (SExternVal (x, t, s))
  | STcInsert(s) ->
      let acc = foldStmt fE fS acc s in
      fS acc (STcInsert s)
  | STyAbbrev(x,def,s) ->
      let acc = foldStmt fE fS acc s in
      fS acc (STyAbbrev (x, def, s))
  | SObjAssign(e1,e2,e3) ->
      let acc = List.fold_left (foldExp fE fS) acc [e1;e2;e3] in
      fS acc (SObjAssign (e1, e2, e3))

(* [e; undefined] is inserted often by LamJS and ImpScript parsing *)
let removeUndefs stmt =
  mapStmt
    (fun x -> x)
    (function
       | SSeq ({stmt = s}, {stmt = SExp {exp = EBase VUndef}}) -> s
       | s -> s)
    stmt
