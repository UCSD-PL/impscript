
open Lang
module P = Printer

type hover_annotation = string

type tooltip = int * int * hover_annotation

type printing_tree =
  | Leaf of string * hover_annotation
  | Inner of printing_tree list * hover_annotation
  | Tab of int
  | Newline

let leaf  ?(ann="") s = Leaf  (s, ann)
let inner ?(ann="") l = Inner (l, ann)

(* TODO some tooltips with semi-colons don't work without leading space
   - seems like "blah;" gets tokenized together, rather than "blah" and ";"
     separately, so without a space the row/col position of the semi-colon
     doesn't match the first character of a token
   - ");" seems to get tokenized into separately
*)
let semi ann = inner [leaf " "; leaf ~ann ";"]

let sepTrees : string -> printing_tree list -> printing_tree =
fun sep trees ->
  let rec foo = function
    | []    -> []
    | t::[] -> [t]
    | t::ts -> t :: leaf sep :: foo ts
  in
  inner (foo trees)

let treeCommas = sepTrees ", "

let rec walkStmt : int -> stmt -> printing_tree =
fun k stmt -> match stmt.stmt with
  | SExp e ->
      inner [walkExp k e; semi "SExp"]
  | SReturn(e) ->
      inner [leaf "return "; walkExp k e; semi "SRet"]
  | SVarDecl (x, {stmt = SVarAssign (x', e)}) when x = x' ->
      inner [leaf (spr "var %s = " x); walkExp k e; semi "SVarInit"]
  | SVarDecl (x, {stmt = SSeq ({stmt=SVarAssign (x', e)}, s)}) when x = x' ->
      inner [
        leaf (spr "var %s = " x); walkExp k e; semi "SVarInit"; Newline;
        Tab k; walkStmt k s
      ]
  | SVarDecl (x, s) ->
      inner [
        leaf (spr "var %s" x); semi "VARDECL"; Newline; Tab k; walkStmt k s
      ]
  | SVarAssign (x, e) ->
      inner [leaf (spr "%s = " x); walkExp k e; semi "VARASSIGN"]
  | SSeq (s1, s2) ->
      inner [walkStmt k s1; Newline; Tab k; walkStmt k s2]
  | SIf (e, s1, s2) ->
      inner [
        leaf "if ("; walkExp k e; leaf ") {"; Newline;
        Tab (succ k); walkStmt (succ k) s1; Newline;
        Tab k; leaf "} else {"; Newline;
        Tab (succ k); walkStmt (succ k) s2; Newline;
        Tab k; leaf ~ann:"SIf" "}"
      ]
  | SWhile (e, s) ->
      inner [
        leaf "while ("; walkExp k e; leaf ") {"; Newline;
        Tab (succ k); walkStmt (succ k) s; Newline;
        Tab k; leaf ~ann:"SWhile" "}"
      ]
  | SLoadedSrc (_, s) -> walkStmt k s (* not using file names... *)
  | SExternVal (x, t, s) ->
      inner [
        leaf (spr "extern val %s : %s;" x (P.strTyp t)); Newline;
        Tab k; walkStmt k s
      ]
  | _ -> failwith (spr "TODO walkStmt %s" (P.strStmtAst stmt))

and walkExp : int -> exp -> printing_tree =
fun k exp -> match exp.exp with
  | EBase v -> Leaf (P.strBaseVal v, "BASETYP " ^ P.strBaseVal v)
  | EVarRead x -> Leaf (x, "VARTYP " ^ x)
  | EFun (xs, body) ->
      inner [
        leaf (spr "function (%s) {" (P.commas xs)); Newline;
        Tab (succ k); walkStmt (succ k) body; Newline;
        Tab k; Leaf ("}", "fall-thru")
      ]
  | EApp (e, es) ->
      let treeFun = walkExp k e in
      let treeArgs = treeCommas (List.map (walkExp k) es) in
      inner [treeFun; leaf " ("; treeArgs; leaf ")"]
  (* TODO annotated functions *)
  | EAs (e, pt) ->
      inner [walkExp k e; leaf (spr " as (%s)" (P.strPreTyp pt))]
  | ECast arrow -> leaf (spr "(%s)" (P.strArrow arrow false))
  | _ -> failwith (spr "TODO walkExp %s" (P.strExpAst exp))

let rec walkTree
  : int -> int -> printing_tree -> (string * int * int * tooltip list) =
fun row col -> function
  | Newline ->
      ("\n", row + 1, 1, [])
  | Tab k ->
      let s = P.tab k in
      (s, row, col + String.length s, [])
  | Leaf (s, ann) ->
      let tips = if ann = "" then [] else [(row, col, ann)] in
      (s, row, col + String.length s, tips)
  | Inner (l, ann) ->
      let tips = if ann = "" then [] else [(row, col, ann)] in
      List.fold_left (fun (acc,row,col,tips) tree ->
        let (s,row,col,tips') = walkTree row col tree in
        (acc ^ s, row, col, tips @ tips')
      ) ("", row, col, tips) l

let printFileAndTooltips oc tree =
  (* 
     - break up s into single-line string literal chunks
     - using single quotes when writing JavaScript to HTML page,
       and double quotes for ImpScript string literals
  *)
  let (s,_,_,tips) = walkTree 1 1 tree in
  let s = Str.global_replace (Str.regexp "\n") "',\n  '" s in

  fpr oc "var arraySrc = [\n";
  fpr oc "  '%s'\n" s;
  fpr oc "];\n";
  fpr oc "\n";
  fpr oc "editor.setValue(arraySrc.join('\\n'));\n";
  fpr oc "editor.gotoLine(0);\n";
  fpr oc "\n";
  fpr oc "clearAnnotations();\n";
  fpr oc "\n";
  List.iter (fun (i,j,s) -> fpr oc "addAnnot(%4d, %3d, '%s');\n" i j s) tips;
  ()

let print stmt fHtml =

  (* TODO directories *)
  let ic = open_in "../ace-output/example.html" in
  let oc = open_out fHtml in

  (* this works only for files tests/blah1/blah2/some-test.js
     TODO compute from fHtml *)
  let acePath = "../../ace-output/" in

  let replace sMatch sReplace s =
    Str.global_replace (Str.regexp sMatch) sReplace s in

  let placeholder = ".*<script src=\"display-file.js\"></script>.*" in
  let rec foo () =
    try
      let s = input_line ic in
      if Str.string_match (Str.regexp placeholder) s 0 then begin
        let tree = walkStmt 0 stmt in
        fpr oc "<script>\n\n";
        printFileAndTooltips oc tree;
        fpr oc "</script>\n";
        foo ();
      end else begin
        let s = replace "src=\"js" (spr "src=\"%sjs" acePath) s in
        let s = replace "href=\"css" (spr "href=\"%scss" acePath) s in
        fpr oc "%s\n" s;
        foo ();
      end
    with End_of_file -> ()
  in
  foo ();

  Log.log1 "Wrote to %s.\n" fHtml;
  ()

