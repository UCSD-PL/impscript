
open Lang

let commas = String.concat ", "

let strLoc = function
  | LConst(x) -> x
  | LVar(x) -> x

let rec strTyp = function
  | TBase(TInt) -> "int"
  | TBase(TNum) -> "num"
  | TBase(TStr) -> "str"
  | TBase(TBool) -> "bool"
  | TBase(TUndef) -> "undefined"
  | TBase(TNull) -> "null"
  | TAny -> "any"
  | TBot -> "bot"
  | TArrow(arrow) -> strArrow arrow true
  | TUnion(ts) -> spr "U (%s)" (String.concat " " (List.map strTyp ts))
  (* | TUnion(ts) -> spr "(%s)" (String.concat " | " (List.map strTyp ts)) *)
  (* | TRefLoc(l) -> spr "ref(%s)" (strLoc l) *)
  (* | TRefLoc(l) -> spr "<%s>" (strLoc l) *)
  | TRefLoc(l) -> spr "*%s" (strLoc l)
  | TExistsRef("L",MuVar(x)) -> x
  | TExistsRef(l,mu) -> spr "exists *%s: %s. ref %s" l (strMu mu) l
  | TMaybe(t) -> spr "?(%s)" (strTyp t)

and strArrow (allLocs,tArgs,h1,someLocs,tRet,h2) flag =
  let input = spr "%s%s%s"
    (if allLocs = [] then "" else spr "all %s. " (commas allLocs))
    (commas (List.map strTyp tArgs))
    (if h1 = [] then "" else spr " / %s" (strHeap h1))
  in
  let output = spr "%s%s%s"
    (if someLocs = [] then "" else spr "some %s. " (commas someLocs))
    (strTyp tRet)
    (if h2 = [] then "" else spr " / %s" (strHeap h2))
  in
  if flag then spr "(%s) -> (%s)" input output  (* type position *)
  else spr "%s => %s" input output              (* cast position *)

and strRecdType (TRecd(width,fields)) =
  let fields = List.sort compare fields in
  spr "{%s%s}"
    (commas (List.map strFieldType fields))
    (match width, fields with
       | ExactDomain, _    -> ""
       | UnknownDomain, [] -> "..."
       | UnknownDomain, _  -> ", ...")

and strHeap h =
  commas (List.map strHeapBinding h)
  (* spr "(%s)" (commas (List.map strHeapBinding h)) *)

and strHeapBinding = function
  | (l,HMu(mu))   -> spr "*%s: %s" (strLoc l) (strMu mu)
  | (l,HRecd(rt)) -> spr "*%s: %s" (strLoc l) (strRecdType rt)

and strMu = function
  (* | Mu("_",rt)     -> strRecdType rt *)
  | Mu(x,rt)       -> spr "mu %s. %s" x (strRecdType rt)
  | MuVar(x)       -> x
  | MuAbbrev(x,[]) -> x
  | MuAbbrev(x,ts) -> spr "%s(%s)" x (commas (List.map strTyp ts))

and strFieldType (f,t) = spr "%s: %s" f (strTyp t)

let strBinding = strFieldType

let strRelySet h =
  spr "{%s}" (commas (List.map strBinding (RelySet.elements h)))

let rec strPreTyp = function
  | Exists(l,pt) -> spr "exists %s. %s" l (strPreTyp pt)
  | Typ(t) -> strTyp t
  | OpenArrow(r,tArgs,tRet) ->
      spr "%s => %s" (strRelySet r) (strTyp (LangUtils.pureArrow tArgs tRet))

let tab k = String.make (2 * k) ' '

let clip = Utils.clip

let intOfNum n =
  let i = int_of_float n in
  if n = float_of_int i then Some i else None

let strBaseVal = function
  | VNum(n)  -> (match intOfNum n with
                   | Some(i) -> string_of_int i
                   | None    -> string_of_float n)
  | VBool(b) -> string_of_bool b
  | VStr(s)  -> spr "\"%s\"" s
  | VUndef   -> "undefined"
  | VNull    -> "null"

let rec strExp k exp = match exp.exp with
  | EBase(v) -> strBaseVal v
  | EVarRead(x) -> x
  | EApp(e,es) ->
      spr "%s(%s)" (strExp k e) (commas (List.map (strExp k) es))
  | EFun(xs,body) ->
      spr "function (%s) {\n%s%s\n%s}" (commas xs)
        (tab (succ k)) (clip (strStmt (succ k) body))
      (tab k)
  (* TODO attach poly arrow inline with func def *)
  (* | EAs({exp=EFun(xs,body)},(Typ(TArrow(tArgs,tRet)) as tArrow)) -> *)
  | EAs({exp=EFun(xs,body)},(Typ(TArrow([],tArgs,[],[],tRet,[])) as tArrow)) ->
      if List.length xs <> List.length tArgs then strEAs k exp tArrow
      else strFunAs k xs body RelySet.empty tArgs tRet
  | EAs({exp=EFun(xs,body)},(OpenArrow(r,tArgs,tRet) as tArrow)) ->
      if List.length xs <> List.length tArgs then strEAs k exp tArrow
      else strFunAs k xs body r tArgs tRet
  | EAs(e,pt) -> strEAs k e pt
  (* | ECast(s,t) -> spr "(%s => %s)" (strTyp s) (strTyp t) *)
  | ECast(arrow) -> spr "(%s)" (strArrow arrow false)
  | ETcErr(s,e,_) -> spr "[[[ %s !!! TC ERROR !!! %s ]]]" (strExp k e) s
  | ETcInsert(e) -> spr "[%s]" (strExp k e)
  | EObj(l) ->
      spr "{%s}" (commas
        (List.map (fun (f, e) -> spr "%s = %s" f (strExp k e)) l))
  | EObjRead(e1,e2) ->
      (match LangUtils.isStr e2 with
        | Some(f) -> spr "%s.%s" (strExp k e1) f
        | None -> spr "%s[%s]" (strExp k e1) (strExp k e2))
  | EFold(mu,e) -> spr "fold (%s, %s)" (strMu mu) (strExp k e)
  | EUnfold(mu,e) -> spr "unfold (%s, %s)" (strMu mu) (strExp k e)

and strFunAs k xs body h tArgs tRet =
  let sHeap = if RelySet.is_empty h then "" else spr "%s " (strRelySet h) in
  let sRet  = strTyp tRet in
  let sArgs = List.map strBinding (List.combine xs tArgs) in
  let sArgs = commas sArgs in
  spr "function %s(%s) -> %s {\n%s%s\n%s}" sHeap sArgs sRet
    (tab (succ k)) (clip (strStmt (succ k) body))
  (tab k)

and strEAs k e pt =
  spr "%s as (%s)" (strExp k e) (strPreTyp pt)
  (* spr "%s as %s" (strExp k e) (strPreTyp pt) *)

and strStmt k stmt = match stmt.stmt with
  | SExp(e) -> spr "%s;" (strExp k e)
  | SReturn(e) -> spr "return %s;" (strExp k e)
  | SVarDecl(x,{stmt=SVarAssign(x',e)}) when x = x' ->
      spr "var %s; %s = %s;" x x (strExp k e)
  | SVarDecl(x,{stmt=SSeq({stmt=SVarAssign(x',e)},s)}) when x = x' ->
      spr "var %s; %s = %s;\n%s%s" x x (strExp k e) (tab k) (strStmt k s)
  | SVarDecl(x,s) -> spr "var %s;\n%s%s" x (tab k) (strStmt k s)
  | SVarAssign(x,e) -> spr "%s = %s;" x (strExp k e)
  (* | SSeq(s0,s) when s0 = LangUtils.sSkip -> spr "%s" (clip (strStmt k s)) *)
  (* | SSeq(s,s0) when s0 = LangUtils.sSkip -> spr "%s" (clip (strStmt k s)) *)
  | SSeq(s1,s2) ->
      spr "%s\n%s%s" (clip (strStmt k s1)) (tab k) (clip (strStmt k s2))
  | SIf(e,s1,s2) ->
        spr "if (%s) {\n"  (strExp k e)
      ^ spr "%s%s\n"       (tab (succ k)) (strStmt (succ k) s1)
      ^ spr "%s} else {\n" (tab k)
      ^ spr "%s%s\n"       (tab (succ k)) (strStmt (succ k) s2)
      ^ spr "%s}"          (tab k)
  | SWhile(e,s) ->
        spr "while (%s) {\n" (strExp k e)
      ^ spr "%s%s\n"         (tab (succ k)) (strStmt (succ k) s)
      ^ spr "%s}"            (tab k)
  | STcInsert({stmt=SVarInvariant(x,t,s)}) ->
      spr "[invariant %s : %s;]\n%s%s" x (strTyp t) (tab k) (strStmt k s)
  | STcInsert({stmt=SClose(xs,s)}) ->
      spr "[close {%s};]\n%s%s" (commas xs) (tab k) (strStmt k s)
  | STcInsert(s) ->
      spr "[%s]" (strStmt k s)
  | SVarInvariant(x,t,s) ->
      spr "invariant %s : %s;\n%s%s" x (strTyp t) (tab k) (strStmt k s)
  | SClose(xs,s) ->
      spr "close {%s};\n%s%s" (commas xs) (tab k) (strStmt k s)
  | SLoadedSrc(f,s) ->
      spr "\n%s(*** %s ***)\n\n%s%s" (tab k) f (tab k) (strStmt k s)
      (* spr "\n%s\n\n%s%s" (tab k) (tab k) (strStmt k s) *)
  | SExternVal(x,t,s) ->
      spr "extern val %s : %s;\n%s%s" x (strTyp t) (tab k) (strStmt k s)
      (* spr "extern val %s : %s\n%s%s" x (strTyp t) (tab k) (strStmt k s) *)
  | STyAbbrev(x,(ys,mu),s) ->
      let tvars = if ys = [] then "" else spr "(%s)" (commas ys) in
        spr "type %s%s = %s;\n" x tvars (strMu mu)
      ^ spr "%s%s"              (tab k) (strStmt k s)
  | SObjAssign(e1,e2,e3) ->
      (match LangUtils.isStr e2 with
        | Some(f) -> spr "%s.%s = %s;" (strExp k e1) f (strExp k e3)
        | None -> spr "%s[%s] = %s;" (strExp k e1) (strExp k e2) (strExp k e3))

let printStmt s f =
  let oc = open_out f in
  fpr oc "%s\n" (strStmt 0 s);
  flush oc;
  Log.log1 "Wrote to %s.\n" f;
  ()

let rec strStmtAst stmt = match stmt.stmt with
  | SExp _ -> "SExp(...)"
  | SReturn _ -> "SReturn(...)"
  | SVarDecl(x,s) -> spr "SVarDecl(%s,%s)" x (strStmtAst s)
  | SVarAssign(x,_) -> spr "SVarAssign(%s,...)" x
  | SSeq(s1,s2) -> spr "SSeq(%s,%s)" (strStmtAst s1) (strStmtAst s2)
  | SExternVal(x,_,s) -> spr "SExternVal(%s,...,%s)" x (strStmtAst s)
  | SLoadedSrc(_,s) -> spr "SLoadedSrc(...,%s)" (strStmtAst s)
  | _ -> "strStmtAst"

let rec strExpAst exp = match exp.exp with
  | EBase _ -> "EBase(...)"
  | EVarRead(x) -> spr "EVarRead(%s)" x
  | EFun _ -> "EFun(...)"
  | EApp _ -> "EApp(...)"
  | EAs(e,_) -> spr "EAs(%s,_)" (strExpAst e)
  | ECast _ -> "ECast(...)"
  | ETcErr _ -> "ETcErr(...)"
  | ETcInsert _ -> "ETcInsert(...)"
  | EObj _ -> "EObj(...)"
  | EObjRead _ -> "EObjRead(...)"
  | EFold _ -> "EFold(...)"
  | EUnfold _ -> "EUnfold(...)"
