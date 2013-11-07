
open Lang

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
  | TArrow(ts,t) ->
      spr "(%s) -> %s" (String.concat ", " (List.map strTyp ts)) (strTyp t)
  | TUnion(ts) ->
      spr "(%s)" (String.concat " | " (List.map strTyp ts))
  | TRefMu(mu) -> spr "ref %s" (strMu mu)
  | TRefLoc(l) -> spr "ref(%s)" (strLoc l)

and strRecdTyp (TRecd(width,fields)) =
  spr "{%s%s}"
    (String.concat ", " (List.map strFieldType fields))
    (match width, fields with
       | ExactDomain, _    -> ""
       | UnknownDomain, [] -> "..."
       | UnknownDomain, _  -> ", ...")

and strMu (x,rt) =
  if x = "_" then strRecdTyp rt
  else spr "mu %s. %s" x (strRecdTyp rt)

and strFieldType (f,t) = spr "%s: %s" f (strTyp t)

let strBinding = strFieldType

let strRelySet h =
  let l = List.map strBinding (RelySet.elements h) in
  spr "{%s}" (String.concat ", " l)

let rec strPreTyp = function
  | Exists(l,pt) -> spr "exists %s. %s" l (strPreTyp pt)
  | Typ(t) -> strTyp t
  | OpenArrow(r,tArgs,tRet) ->
      spr "%s => %s" (strRelySet r) (strTyp (TArrow (tArgs, tRet)))

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
      spr "%s(%s)" (strExp k e) (String.concat ", " (List.map (strExp k) es))
  | EFun(xs,body) ->
      spr "function (%s) {\n%s%s\n%s}" (String.concat ", " xs)
        (tab (succ k)) (clip (strStmt (succ k) body))
      (tab k)
  | EAs({exp=EFun(xs,body)},(Typ(TArrow(tArgs,tRet)) as tArrow)) ->
      if List.length xs <> List.length tArgs then strEAs k exp tArrow
      else strFunAs k xs body RelySet.empty tArgs tRet
  | EAs({exp=EFun(xs,body)},(OpenArrow(r,tArgs,tRet) as tArrow)) ->
      if List.length xs <> List.length tArgs then strEAs k exp tArrow
      else strFunAs k xs body r tArgs tRet
  | EAs(e,pt) -> strEAs k e pt
  | ECast(s,t) -> spr "(%s => %s)" (strTyp s) (strTyp t)
  | ETcErr(s,e,_) -> spr "[[[ %s !!! TC ERROR !!! %s ]]]" (strExp k e) s
  | ETcInsert(e) -> spr "[%s]" (strExp k e)
  | EObj(l) ->
      spr "{%s}" (String.concat ", "
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
  let sArgs = String.concat ", " sArgs in
  spr "function %s(%s) -> %s {\n%s%s\n%s}" sHeap sArgs sRet
    (tab (succ k)) (clip (strStmt (succ k) body))
  (tab k)

and strEAs k e pt = spr "%s as %s" (strExp k e) (strPreTyp pt)

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
      spr "[close {%s};]\n%s%s" (String.concat ", " xs) (tab k) (strStmt k s)
  | STcInsert(s) ->
      spr "[%s]" (strStmt k s)
  | SVarInvariant(x,t,s) ->
      spr "invariant %s : %s;\n%s%s" x (strTyp t) (tab k) (strStmt k s)
  | SClose(xs,s) ->
      spr "close {%s};\n%s%s" (String.concat ", " xs) (tab k) (strStmt k s)
  | SLoadedSrc(f,s) ->
      spr "\n%s(*** %s ***)\n\n%s%s" (tab k) f (tab k) (strStmt k s)
      (* spr "\n%s\n\n%s%s" (tab k) (tab k) (strStmt k s) *)
  | SExternVal(x,t,s) ->
      spr "extern val %s : %s\n%s%s" x (strTyp t) (tab k) (strStmt k s)
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
