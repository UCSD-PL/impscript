
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

let hideInComment ?(trySingleLine=true) tr = HideInComment (trySingleLine, tr)

let tcInserted ?(trySingleLine=true) tr    = hideInComment ~trySingleLine tr
 (* if want to distinguish the kind of comments,
    add something like "[...]" around "inferred" beforehand *)

let sepTrees : printing_tree -> printing_tree list -> printing_tree =
fun sep trees ->
  let rec foo = function
    | []    -> []
    | t::[] -> [t]
    | t::ts -> t :: sep :: foo ts
  in
  inner (foo trees)

let treeCommas = sepTrees (leaf " , ") (* space before "," *)

let treeCommasAndNewlines k = sepTrees (inner [leaf " ,"; Newline; Tab k])

(* ImpScript type variable syntax conflicts with JavaScript string literals.
   TODO for compatibility with the HTML files, could change ImpScript to parse
   backquote and turn it into single quote. *)
let replacePrimes s =
  Str.global_replace (Str.regexp "'") "`" s

let strPairHeapEnvBinding = function
  | (l, HEMu mu   ) -> (spr "*%s" (P.strLoc l), spr " : %s" (P.strMu mu))
  | (l, HERecd rt ) -> (spr "*%s" (P.strLoc l), spr " : %s" (P.strRecdType rt))
  | (l, HEProxy l') -> (spr " %s" (P.strLoc l), spr " > %s" (P.strLoc l'))

let strHeapEnv he =
  let width = ref 0 in (* length of widest domain string *)
  let recordWidth s =
    if String.length s > !width then width := String.length s;
    s
  in
  []
  |> VarMap.fold (fun x pt acc ->
       (recordWidth (spr "*%s" x), spr " : %s" (P.strPreTyp pt)) :: acc
     ) he.vars
  |> LocMap.fold (fun l heb acc ->
       let (s1, s2) = strPairHeapEnvBinding (l, heb) in
       let _ = recordWidth s1 in
       (s1, s2) :: acc
     ) he.locs
  |> List.rev
  |> List.map (fun (s1,s2) -> spr "%*s%s" (-1 * !width) s1 s2)
  |> String.concat "\n" (* newlines will get removed by printFileAndTooltips *)

let strWorldEnv stmt =
  spr "%s\n\n%s" (P.strPreTyp stmt.pt_s) (strHeapEnv stmt.he_s)

let rec containsNewline = function
  | Newline -> true
  | Leaf _ | Tab _ -> false
  | HighlightError tr | HideInComment (_, tr) -> containsNewline tr
  | Inner (l, _) -> List.exists containsNewline l

let rec walkStmt : int -> stmt -> printing_tree =
fun k stmt -> match stmt.stmt with

  | SBlankLine -> leaf ""

  | SExp e ->
      inner [walkExp k e; semi (strWorldEnv stmt)]

  | SReturn e ->
      inner [
        leaf ~ann:stmt.extra_info_s "return ";
        walkExp k e; semi (strWorldEnv stmt)
      ]

  | SVarDecl (x, ({stmt = SVarAssign (x', e)} as s0)) when x = x' ->
      inner [leaf (spr "var %s = " x); walkExp k e; semi (strWorldEnv s0)]

  | SVarDecl (x, {stmt = SSeq (({stmt = SVarAssign (x', e)} as s1), s2)})
        when x = x' -> begin
      match e.exp with
       | EAs (({exp = EFun _} as eFun), pt) ->
           (* strip annotation, and use sSeq to put sequence back together.
              sSeq inserts dummy info, okay b/c printing SSeq doesn't use it. *)
           let s1 = {s1 with stmt = SVarAssign (x, eFun)} in
           let stmt = {stmt with stmt = SVarDecl (x, LangUtils.sSeq [s1;s2])} in
           inner [
             hideInComment (leaf (spr "%s :: %s" x (P.strPreTyp pt)));
             Newline; walkStmt k stmt
           ]
       | _ ->
           inner [
             leaf (spr "var %s = " x); walkExp k e; semi (strWorldEnv s1);
             Newline; Tab k; walkStmt k s2
           ]
    end

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
        hideInComment (leaf (spr "extern val %s : %s ;" x (P.strTyp t)));
        Newline; Tab k; walkStmt k s
      ]

  | SMuAbbrev (x, (ys, mu), s) ->
      let tvars = if ys = [] then "" else spr "(%s)" (P.commas ys) in
      inner [
        hideInComment (leaf (spr "type %s%s = %s ;" x tvars (P.strMu mu)));
        Newline; Tab k; walkStmt k s
      ]

  | STcInsert ({stmt = SSeq (s1, s2)}) ->
      inner [
        tcInserted (walkStmt k s1); Newline;
        Tab k; walkStmt k s2
      ]

  | STcInsert ({stmt = SVarInvariant (x, t, s)} as s0) ->
      inner [
        tcInserted
          (inner [leaf (spr "invariant %s : %s" x (P.strTyp t));
                  semi s0.extra_info_s]);
        Newline; Tab k; walkStmt k s
      ]

  | STcInsert ({stmt = SClose (xs, s)} as s0) ->
      inner [
        tcInserted
          (inner [leaf (spr "close {%s}" (P.commas xs));
                  semi s0.extra_info_s]);
        Newline; Tab k; walkStmt k s
      ]

  | STcInsert s ->
      tcInserted (walkStmt k s)

  | SVarInvariant (x, t, s) ->
      inner [
        leaf (spr "invariant %s : %s" x (P.strTyp t)); semi stmt.extra_info_s;
        Newline; Tab k; walkStmt k s
      ]

  | SClose (xs, s) ->
      inner [
        leaf (spr "close {%s}" (P.commas xs)); semi stmt.extra_info_s;
        Newline; Tab k; walkStmt k s
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
        treeFun; leaf " "; leaf ~ann:exp.extra_info_e "(";
        treeArgs; leaf ~ann:(P.strPreTyp exp.pt_e) ")"
      ]

  | EAs (e, pt) ->
      inner [
        hideInComment ~trySingleLine:false (leaf (P.strPreTyp pt)); leaf " ";
        walkExp k e
      ]

  | ECast arrow ->
      leaf (spr "(%s)" (P.strArrow arrow false))

  | EObj [] ->
      leaf ~ann:(P.strPreTyp exp.pt_e) "{}"

(*
  | EObj fes ->
      (* could insert Newlines when expressions are too long *)
      let l =
        List.map
          (fun (f,e) -> inner [leaf (spr "%s = " f); walkExp k e]) fes in
      let ann = P.strPreTyp exp.pt_e in
      inner ~ann [leaf "{ "; treeCommas l; leaf " }"]
*)

  | EObj fes ->
      let walkFields k =
        List.map
          (fun (f,e) -> inner [leaf (spr "%s = " f); walkExp k e]) fes in
      let ann = P.strPreTyp exp.pt_e in
      let res = inner [leaf ~ann "{ "; treeCommas (walkFields k); leaf " }"] in
      if not (containsNewline res) then
        res
      else
        inner [
          leaf ~ann "{"; Newline;
          Tab (succ k); treeCommasAndNewlines (succ k) (walkFields (succ k));
          Newline; Tab k; leaf "}"
        ]

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
      let ann = exp.extra_info_e in
      inner [leaf (spr "fold (%s, " (P.strMu mu)); walkExp k e; leaf ~ann ")"]

  | EUnfold (mu, e) ->
      let ann = exp.extra_info_e in
      inner [leaf (spr "unfold (%s, " (P.strMu mu)); walkExp k e; leaf ~ann ")"]

  (* Tc.genSym names temporaries starting with "__" *)
  | ETcInsert {exp = ELet (x, e1, e2)} when Utils.strPrefix x "__" ->
      inner [
        tcInserted ~trySingleLine:false (leaf (spr "let %s =" x));
        leaf " "; walkExp k e1; leaf " ";
        tcInserted ~trySingleLine:false
          (inner [leaf "in "; leaf "("; walkExp k e2; leaf ")"])
      ]

  (* Tc.inlineUnfold *)
  | ETcInsert {exp = ELet ("_",
        ({exp = EUnfold (_, {exp = EVarRead x})} as eUn),
        ({exp = EVarRead x'} as eX))} when x = x' ->
      inner [
        tcInserted ~trySingleLine:false
          (inner [leaf "let _ = "; walkExp k eUn; leaf " in ("]);
        leaf " "; walkExp k eX; leaf " ";
        tcInserted ~trySingleLine:false (leaf ")")
      ]

  | ETcInsert e ->
      tcInserted ~trySingleLine:false (walkExp k e)

  (* NOTE
     - keep this in sync with Tc
     - bare ELet should appear only inside a sequence of tc-inserted inline
       folds, so don't add any nested comments *)
  | ELet (x, e1, e2) ->
      if x = "_" then
        inner [walkExp k e1; leaf "; "; walkExp k e2]
      else
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

