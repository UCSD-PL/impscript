
open Lang

let wrapExp e = {
  exp = e;
  pt_e = Typ TPlaceholder;
  extra_info_e = ""
}

let eFun xs s      = wrapExp (EFun (xs, s))
let eStr s         = wrapExp (EBase (VStr s))
let eBool b        = wrapExp (EBase (VBool b))
let eInt n         = wrapExp (EBase (VNum (float_of_int n)))
let eNull          = wrapExp (EBase (VNull))
let eUndef         = wrapExp (EBase (VUndef))
let eVar x         = wrapExp (EVarRead x)
let eApp e es      = wrapExp (EApp (e, es))
let eAs e t        = wrapExp (EAs (e, t))
let eCast s t      = wrapExp (ECast (([], [s], []), ([], t, [])))
let ePolyCast arr  = wrapExp (ECast arr)
let eObj l         = wrapExp (EObj l)
let eGet e1 e2     = wrapExp (EObjRead (e1, e2))
let eFold mu e     = wrapExp (EFold (mu, e))
let eUnfold mu e   = wrapExp (EUnfold (mu, e))
let eTcInsert e    = wrapExp (ETcInsert e)
let eLet x e1 e2   = wrapExp (ELet (x, e1, e2))

let wrapStmt s = {
  stmt = s;
  pt_s = Typ TPlaceholder;
  he_s = emptyHeapEnv;
  extra_info_s = ""
}

let sRet e         = wrapStmt (SReturn e)
let sLetRef x s    = wrapStmt (SVarDecl (x, s))
let sAssign x e    = wrapStmt (SVarAssign (x, e))
let sInvar x t s   = wrapStmt (SVarInvariant (x, t, s))
let sClose xs s    = wrapStmt (SClose (xs, s))
let sIf e s1 s2    = wrapStmt (SIf (e, s1, s2))
let sWhile e s     = wrapStmt (SWhile (e, s))
let sLoaded f s    = wrapStmt (SLoadedSrc (f, s))
let sExtern x t s  = wrapStmt (SExternVal (x, t, s))
let sMuDef x y s   = wrapStmt (SMuAbbrev (x, y, s))
let sExp e         = wrapStmt (SExp e)
let sSet e1 e2 e3  = wrapStmt (SObjAssign (e1, e2, e3))
let sTcInsert s    = wrapStmt (STcInsert s)
let sBlankLine     = wrapStmt SBlankLine
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

let pureArrow tArgs tRet = TArrow (([], tArgs, []), ([], tRet, []))

let finishArrow r arrow =
  if RelySet.is_empty r then Typ (TArrow arrow) else OpenArrow (r, arrow)

let isStr = function
  | {exp=EBase(VStr(s))} -> Some s
  | _ -> None

(* might want to include an fT parameter for these mappers *)

let rec mapExp fE fS exp =
  {exp with exp = mapExp_ fE fS exp.exp}

and mapStmt fE fS stmt =
  {stmt with stmt = mapStmt_ fE fS stmt.stmt}

and mapExp_ fE fS = function
  | EBase(v) -> fE (EBase v)
  | EVarRead(x) -> fE (EVarRead x)
  | EFun(xs,s) -> fE (EFun (xs, mapStmt fE fS s))
  | EApp(e,es) -> fE (EApp (mapExp fE fS e, List.map (mapExp fE fS) es))
  | EAs(e,t) -> fE (EAs (mapExp fE fS e, t))
  | ECast(arrow) -> fE (ECast arrow)
  | ETcErr(s,e,so) -> fE (ETcErr (s, mapExp fE fS e, so)) (* skipping so *)
  | ETcInsert(e) -> fE (ETcInsert (mapExp fE fS e))
  | EObj(l) -> fE (EObj (List.map (fun (f,e) -> (f, mapExp fE fS e)) l))
  | EObjRead(e1,e2) -> fE (EObjRead (mapExp fE fS e1, mapExp fE fS e2))
  | EFold(mu,e) -> fE (EFold (mu, mapExp fE fS e))
  | EUnfold(mu,e) -> fE (EUnfold (mu, mapExp fE fS e))
  | ELet(x,e1,e2) -> fE (ELet (x, mapExp fE fS e1, mapExp fE fS e2))

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
  | SBlankLine -> fS SBlankLine
  | SMuAbbrev(x,def,s) -> fS (SMuAbbrev (x, def, mapStmt fE fS s))
  | SObjAssign(e1,e2,e3) ->
      fS (SObjAssign (mapExp fE fS e1, mapExp fE fS e2, mapExp fE fS e3))

type mappers = {
  fT  : typ -> typ;
  fMu : mu_type -> mu_type;
}

let emptyMappers = {
  fT  = (fun x -> x);
  fMu = (fun x -> x);
}

let rec mapTyp foo typ =
  let fT = foo.fT in
  match typ with
   | TBase bt -> fT (TBase bt)
   | TArrow ((allLocs,ts,h1), (someLocs,t,h2)) ->
       let (ts,t) = (List.map (mapTyp foo) ts, mapTyp foo t) in
       let (h1,h2) = (mapHeap foo h1, mapHeap foo h2) in
       fT (TArrow ((allLocs, ts, h1), (someLocs, t, h2)))
   | TUnion ts -> fT (TUnion (List.map (mapTyp foo) ts))
   | TAny -> fT TAny
   | TBot -> fT TBot
   | TMaybe t -> fT (TMaybe (mapTyp foo t))
   | TRefLoc l -> fT (TRefLoc l)
   | TExistsRef (l, mu) -> fT (TExistsRef (l, mapMuType foo mu))
   | TPlaceholder -> fT TPlaceholder

and mapHeap foo =
  List.map (function
    | (l, HRecd rt) -> (l, HRecd (mapRecdType foo rt))
    | (l, HMu mu)   -> (l, HMu (mapMuType foo mu))
  )

and mapRecdType foo (TRecd (width, fts)) =
  TRecd (width, List.map (fun (x, t) -> (x, mapTyp foo t)) fts)

and mapMuType foo mu =
  let fMu = foo.fMu in
  match mu with
    | Mu (x, rt)       -> fMu (Mu (x, mapRecdType foo rt))
    | MuVar x          -> fMu (MuVar x)
    | MuAbbrev (x, ts) -> fMu (MuAbbrev (x, List.map (mapTyp foo) ts))

let simpleMapTyp fT = mapTyp { emptyMappers with fT = fT }

let rec foldExp fE fS acc {exp=e} = foldExp_ fE fS acc e

and foldStmt fE fS acc {stmt=s} = foldStmt_ fE fS acc s

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
  | ECast(arrow) ->
      fE acc (ECast arrow)
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
  | ELet(x,e1,e2) ->
      let acc = List.fold_left (foldExp fE fS) acc [e1;e2] in
      fE acc (ELet (x, e1, e2))

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
  | SMuAbbrev(x,def,s) ->
      let acc = foldStmt fE fS acc s in
      fS acc (SMuAbbrev (x, def, s))
  | SObjAssign(e1,e2,e3) ->
      let acc = List.fold_left (foldExp fE fS) acc [e1;e2;e3] in
      fS acc (SObjAssign (e1, e2, e3))
  | SBlankLine ->
      fS acc SBlankLine

(* [e; undefined] is inserted often by LamJS and ImpScript parsing *)
let removeUndefs stmt =
  mapStmt
    (fun x -> x)
    (function
       | SSeq ({stmt = s}, {stmt = SExp {exp = EBase VUndef}}) -> s
       | s -> s)
    stmt
