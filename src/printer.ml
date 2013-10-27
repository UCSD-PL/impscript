
open Lang

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
  | EAs({exp=EFun(xs,body)},(TArrow(tArgs,tRet) as tArrow)) ->
      if List.length xs <> List.length tArgs then strEAs k exp tArrow
      else
        let sRet = strTyp tRet in
        let sArgs = List.map (fun (x,t) -> spr "%s: %s" x (strTyp t))
                      (List.combine xs tArgs) in
        spr "function (%s) -> %s {\n%s%s\n%s}" (String.concat ", " sArgs) sRet
          (tab (succ k)) (clip (strStmt (succ k) body))
        (tab k)
  | EAs(e,t) -> strEAs k e t
  | ECast(s,t) -> spr "(%s => %s)" (strTyp s) (strTyp t)
  (* | ECast(s,t) -> Utils.redString (spr "(%s => %s)" (strTyp s) (strTyp t)) *)

and strEAs k e t = spr "%s as %s" (strExp k e) (strTyp t)

and strStmt k stmt = match stmt.stmt with
  | SExp(e) -> spr "%s;" (strExp k e)
  | SReturn(e) -> spr "return %s;" (strExp k e)
  | SVarDecl(x,{stmt=SVarAssign(x',e)}) when x = x' ->
      spr "var %s; %s = %s;" x x (strExp k e)
  | SVarDecl(x,{stmt=SSeq({stmt=SVarAssign(x',e)},s)}) when x = x' ->
      spr "var %s; %s = %s;\n%s%s" x x (strExp k e) (tab k) (strStmt k s)
  | SVarDecl(x,s) -> spr "var %s;\n%s%s" x (tab k) (strStmt k s)
  | SVarAssign(x,e) -> spr "%s = %s;" x (strExp k e)
  (* | SSeq({stmt=SVarDecl _},{stmt=SVarAssign _}) -> failwith "a" *)
  | SSeq(s1,s2) ->
      spr "%s\n%s%s" (clip (strStmt k s1)) (tab k) (clip (strStmt k s2))
  | SIf(e,s1,s2) ->
        spr "if (%s) {\n"  (strExp k e)
      ^ spr "%s%s\n"       (tab (succ k)) (strStmt (succ k) s1)
      ^ spr "%s} else {\n" (tab k)
      ^ spr "%s%s\n"       (tab (succ k)) (strStmt (succ k) s2)
      ^ spr "%s}"          (tab k)
  | SWhile _ -> failwith "can't print"
  | SVarInvariant(x,t,s) ->
      spr "invariant %s : %s\n%s%s" x (strTyp t) (tab k) (strStmt k s)
  | SLoadedSrc(f,s) ->
      spr "\n%s(*** %s ***)\n\n%s%s" (tab k) f (tab k) (strStmt k s)
  | SExternVal(x,t,s) ->
      spr "extern val %s : %s\n%s%s" x (strTyp t) (tab k) (strStmt k s)

let printStmt s f =
  (* let oc = open_out (Settings.out_dir ^ "out.is") in *)
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
  | _ -> spr "strStmtAst"
