
open Lang
module P = Printer

(*
  NOTES

  - walkStmt and walkExp should always use Newlines, not "\n" string literals

  TODOS

  - some tooltips with semi-colons don't work without leading space
  - seems like "blah;" gets tokenized together, rather than "blah" and ";"
    separately, so without a space the row/col position of the semi-colon
    doesn't match the first character of a token
  - ");" seems to get tokenized into separately

  - "." doesn't get tokenized as first character either
  - so for now, using bracket notation to print EObjRead and SObjAssign

  - in treeCommas, adding a leading space because things like "1," get
    tokenized as a single token
*)

type hover_annotation = string

type tooltip = int * int * hover_annotation

type row = int

type col = int

type highlight_range = (row * col) * (row * col)

type printing_tree =
  | Leaf of string * hover_annotation
  | Inner of printing_tree list * hover_annotation
  | Tab of int
  | Newline
  | HighlightError of printing_tree
  | HideInComment of bool * printing_tree
      (* flag signifies whether to try to use single-line JS comment *)

let leaf  ?(ann="") s = Leaf  (s, ann)
let inner ?(ann="") l = Inner (l, ann)

let semi ann = inner [leaf " "; leaf ~ann ";"] (* space before ";" *)

let hideInComment tr       = HideInComment (true, tr)
let hideInCommentSingle tr = HideInComment (false, tr)

let sepTrees : string -> printing_tree list -> printing_tree =
fun sep trees ->
  let rec foo = function
    | []    -> []
    | t::[] -> [t]
    | t::ts -> t :: leaf sep :: foo ts
  in
  inner (foo trees)

let treeCommas = sepTrees " , " (* space before "," *)

(* ImpScript type variable syntax conflicts with JavaScript string literals.
   TODO for compatibility with the HTML files, could change ImpScript to parse
   backquote and turn it into single quote. *)
let replacePrimes s =
  Str.global_replace (Str.regexp "'") "`" s

let strHeapEnvBinding = function
  | HMu mu   -> P.strMu mu
  | HRecd rt -> P.strRecdType rt

let strHeapEnv he =
  let width = ref 0 in (* length of widest domain string *)
  let strHeapBind s =
    let s = spr "*%s" s in
    if String.length s > !width then width := String.length s;
    s
  in
  []
  |> VarMap.fold (fun x pt acc ->
       (strHeapBind x, spr " : %s" (P.strPreTyp pt)) :: acc
     ) he.vars
  |> LocMap.fold (fun l hb acc ->
       (strHeapBind (P.strLoc l), spr " : %s" (strHeapEnvBinding hb)) :: acc
     ) he.locs
  |> List.rev
  |> List.map (fun (s1,s2) -> spr "%*s%s" (-1 * !width) s1 s2)
  |> String.concat "\n" (* newlines will get removed by printFileAndTooltips *)

let strWorldEnv stmt =
  spr "%s\n\n%s" (P.strPreTyp stmt.pt_s) (strHeapEnv stmt.he_s)

let rec walkStmt : int -> stmt -> printing_tree =
fun k stmt -> match stmt.stmt with
  | SExp e ->
      inner [walkExp k e; semi (strWorldEnv stmt)]
  | SReturn(e) ->
      inner [leaf "return "; walkExp k e; semi (strWorldEnv stmt)]
  | SVarDecl (x, ({stmt = SVarAssign (x', e)} as s0)) when x = x' ->
      inner [leaf (spr "var %s = " x); walkExp k e; semi (strWorldEnv s0)]
  | SVarDecl (x, {stmt = SSeq (({stmt=SVarAssign (x', e)} as s0), s)}) when x = x' ->
      inner [
        leaf (spr "var %s = " x); walkExp k e; semi (strWorldEnv s0); Newline;
        Tab k; walkStmt k s
      ]
  | SVarDecl (x, s) ->
      inner [leaf (spr "var %s" x); semi ""; Newline; Tab k; walkStmt k s]
  | SVarAssign (x, e) ->
      inner [leaf (spr "%s = " x); walkExp k e; semi (strWorldEnv stmt)]
  | SObjAssign (e1, e2, e3) -> begin
      match LangUtils.isStr e2 with
        (* | Some f ->
            inner [
              walkExp k e1; leaf (spr ".%s = " f); walkExp k e3;
              semi (strWorldEnv stmt)
            ] *)
        | _ ->
            inner [
              walkExp k e1; leaf "["; walkExp k e2; leaf "]"; leaf " = ";
              walkExp k e3; semi (strWorldEnv stmt)
            ]
    end
  | SSeq (s1, s2) ->
      inner [walkStmt k s1; Newline; Tab k; walkStmt k s2]
  | SIf (e, s1, s2) ->
      inner [
        leaf "if ("; walkExp k e; leaf ") {"; Newline;
        Tab (succ k); walkStmt (succ k) s1; Newline;
        Tab k; leaf "} else {"; Newline;
        Tab (succ k); walkStmt (succ k) s2; Newline;
        Tab k; leaf ~ann:(strWorldEnv stmt) "}"
      ]
  | SWhile (e, s) ->
      inner [
        leaf "while ("; walkExp k e; leaf ") {"; Newline;
        Tab (succ k); walkStmt (succ k) s; Newline;
        Tab k; leaf ~ann:(strWorldEnv stmt) "}"
      ]
  | SLoadedSrc (_, s) -> (* not using file names... *)
      walkStmt k s
  | SExternVal (x, t, s) ->
      inner [
        leaf (spr "extern val %s : %s;" x (P.strTyp t)); Newline;
        Tab k; walkStmt k s
      ]
  | SMuAbbrev (x, (ys, mu), s) ->
      let tvars = if ys = [] then "" else spr "(%s)" (P.commas ys) in
      inner [
        leaf (spr "type %s%s = %s;" x tvars (P.strMu mu)); Newline;
        Tab k; walkStmt k s
      ]
  | STcInsert ({stmt = SSeq (s1, s2)}) ->
      inner [
        hideInComment (walkStmt k s1); Newline;
        Tab k; walkStmt k s2
      ]
  | STcInsert ({stmt = SVarInvariant (x, t, s)}) ->
      inner [
        hideInComment
          (inner [leaf (spr "invariant %s : %s" x (P.strTyp t)); semi "TODO"]);
        Newline; Tab k; walkStmt k s
      ]
  | STcInsert ({stmt = SClose (xs, s)}) ->
      inner [
        hideInComment
          (inner [leaf (spr "close {%s}" (P.commas xs)); semi "TODO"]);
        Newline; Tab k; walkStmt k s
      ]
  | STcInsert s ->
      hideInComment (walkStmt k s)
  | SVarInvariant (x, t, s) ->
      inner [
        leaf (spr "invariant %s : %s" x (P.strTyp t)); semi "TODO"; Newline;
        Tab k; walkStmt k s
      ]
  | SClose (xs, s) ->
      inner [
        leaf (spr "close {%s}" (P.commas xs)); semi "TODO"; Newline;
        Tab k; walkStmt k s
      ]

and walkExp : int -> exp -> printing_tree =
fun k exp -> match exp.exp with
  | EBase v ->
      leaf ~ann:(P.strPreTyp exp.pt_e) (P.strBaseVal v)
  | EVarRead x ->
      leaf ~ann:(P.strPreTyp exp.pt_e) x
  | EFun (xs, body) ->
      inner [
        leaf (spr "function (%s) {" (P.commas xs)); Newline;
        Tab (succ k); walkStmt (succ k) body; Newline;
        Tab k; leaf ~ann:(strWorldEnv body) "}"
      ]
  | EApp (e, es) ->
      let treeFun = walkExp k e in
      let treeArgs = treeCommas (List.map (walkExp k) es) in
      inner [
        treeFun; leaf " "; leaf ~ann:"TODO" "(";
        treeArgs; leaf ~ann:(P.strPreTyp exp.pt_e) ")"
      ]
  (* TODO annotated functions *)
  | EAs (e, pt) ->
      inner [walkExp k e; leaf (spr " as (%s)" (P.strPreTyp pt))]
  | ECast arrow ->
      leaf (spr "(%s)" (P.strArrow arrow false))
  | EObj [] ->
      leaf ~ann:(P.strPreTyp exp.pt_e) "{}"
  | EObj fes ->
      (* could insert Newlines when expressions are too long *)
      let l =
        List.map
          (fun (f,e) -> inner [leaf (spr "%s = " f); walkExp k e]) fes in
      let ann = P.strPreTyp exp.pt_e in
      inner ~ann [leaf "{ "; treeCommas l; leaf " }"]
  | EObjRead (e1, e2) ->
      let ann = P.strPreTyp exp.pt_e in
      (match LangUtils.isStr e2 with
        (* | Some f -> inner ~ann [walkExp k e1; leaf "."; leaf f] *)
        | _  -> inner [walkExp k e1; leaf "["; walkExp k e2; leaf ~ann "]"])
  | ETcErr (ann, {exp = EBase VStr "XXX"}, _) -> (* see Typing.sTcErr *)
      HighlightError (inner [
        leaf "!!! "; leaf ~ann "TC_ERROR"; leaf " !!!"
      ])
  | ETcErr (ann, e, _) ->
      HighlightError (inner [
        leaf "!!! "; leaf ~ann "TC_ERROR";
        leaf " ( "; walkExp k e; leaf " ) !!!"
      ])
  | EFold (mu, e) ->
      inner [leaf (spr "fold (%s, " (P.strMu mu)); walkExp k e; leaf ")"]
  | EUnfold (mu, e) ->
      inner [leaf (spr "unfold (%s, " (P.strMu mu)); walkExp k e; leaf ")"]
  | ETcInsert e ->
      hideInCommentSingle (walkExp k e)
  | ELet (x, e1, e2) ->
      inner [
        leaf (spr "let %s = " x); walkExp k e1; leaf " in ";
        leaf "("; walkExp k e2; leaf ")"
      ]

let rec walkTree
  : int -> int -> printing_tree
 -> (string * int * int * tooltip list * highlight_range list) =
fun row col -> function

  | Newline ->
      ("\n", row + 1, 1, [], [])

  | Tab k ->
      let s = P.tab k in
      (s, row, col + String.length s, [], [])

  | Leaf (s, ann) ->
      let tips = if ann = "" then [] else [(row, col, ann)] in
      (s, row, col + String.length s, tips, [])

  | Inner (l, ann) ->
      let tips = if ann = "" then [] else [(row, col, ann)] in
      List.fold_left (fun (acc,row,col,tips,ranges) tree ->
        let (s,row,col,tips',ranges') = walkTree row col tree in
        (acc ^ s, row, col, tips @ tips', ranges @ ranges')
      ) ("", row, col, tips, []) l

  | HighlightError tr ->
      let (s,row',col',tips,ranges) = walkTree row col tr in
      let highlightRange = ((row-1, col-1), (row'-1, col'-1)) in
      (s, row', col', tips, highlightRange :: ranges)

  | HideInComment (trySingleLine, tr) ->
      let (pre,suf) = ("/*: ", " */") in
      let preSingle = ("//: ") in
      let len = String.length in
      let _ = assert (len preSingle = len pre) in
      let (s,row',col',tips,ranges) = walkTree row (col + len pre) tr in

      (* choose either multi- or single-line comment *)
      if Str.string_match (Str.regexp ".*\n") s 0 || trySingleLine = false
      then (spr "%s%s%s" pre s suf, row', col' + len suf, tips, ranges)
      else (spr "%s%s" preSingle s, row', col'          , tips, ranges)

let printFileAndTooltips oc tree =
  (* 
     - break up s into single-line string literal chunks
     - using single quotes when writing JavaScript to HTML page,
       and double quotes for ImpScript string literals
  *)
  let (s,_,_,tips,ranges) = walkTree 1 1 tree in
  let s = replacePrimes s in
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

  List.iter (fun (i,j,s) ->
    let s = replacePrimes s in
    let l = Str.split (Str.regexp "\n") s in
    if List.length l <= 1 then
      fpr oc "addAnnot(%d, %d, '%s');\n\n" i j s
    else begin
      fpr oc "addAnnot(%d, %d, [\n" i j;
      List.iter (fun s -> fpr oc "  '%s',\n" s) l;
      fpr oc "].join('\\n'));\n\n";
    end
  ) tips;

  (* instead, could track using data constructors for hover_annotation
     List.iter
       (fun (i,j,s) -> fpr oc "addAnnot(%4d, %3d, '%s');\n" i j s) tips; *)

  List.iter (fun ((r1,c1), (r2,c2)) ->
    let sRange = spr "new Range(%d, %d, %d, %d)" r1 c1 r2 c2 in
    fpr oc "editor.session.addMarker(%s, 'ace_step', 'error');\n\n" sRange
  ) ranges;

  ()

let replace sMatch sReplace s =
  Str.global_replace (Str.regexp sMatch) sReplace s

let print stmt fHtml =

  let ic = open_in (Settings.ace_dir ^ "example.html") in
  let oc = open_out fHtml in
  let acePath = "../../ace-output/" in
        (* this works only for files tests/blah1/blah2/some-test.js
           TODO compute from fHtml *)

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
  fpr (open_out Settings.out_html_filename) "%s\n" fHtml;
  ()

