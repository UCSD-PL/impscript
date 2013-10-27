
open Lexing

let pr = Printf.printf
let spr = Printf.sprintf


(***** Command-line options ***************************************************)

let srcFiles  = ref []

let usage = "\nUsage: ./impscript [options] (src_file.js | src_file.n.is)\n"

let argSpecs = [
  ("-parseOnly", Arg.Set Settings.parseOnly,
              "");
(*
  ("-checkingMode", Arg.Unit (fun () -> Settings.castInsertionMode := false),
                 "     check program without inserting casts");
*)
]

let anonArgFun s =
  srcFiles := !srcFiles @ [s]

let stripSuffix s suf =
  if Str.string_match (Str.regexp (spr "\\(.*\\)%s$" suf)) s 0
  then Some (Str.matched_group 1 s)
  else None

let stripNumericSuffix s =
  if Str.string_match (Str.regexp "\\(.*\\)[.]\\([0-9]+\\)$" ) s 0
  then Some (Str.matched_group 1 s, int_of_string (Str.matched_group 2 s))
  else None


(***** Parsing ****************************************************************)

let string_of_position (p, e) = 
  Format.sprintf "%s:%d:%d-%d" p.pos_fname p.pos_lnum
    (p.pos_cnum - p.pos_bol) (e.pos_cnum - e.pos_bol)

(* rkc: handling position info similar to Lambdajs.parse_lambdajs and
   Lambdajs_env.parse_env *)
let doParse start_production name =
  let lexbuf = Lexing.from_channel (open_in name) in
  let strPos () = string_of_position (lexbuf.lex_curr_p, lexbuf.lex_curr_p) in
    try begin
      (* Set the correct filename in lexbuf (for source-tracking). *)
      lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with
                               pos_fname = name; pos_lnum = 1 };
      start_production LangLexer.token lexbuf
    end with
      | Failure "lexing: empty token" ->
          Log.printParseErr (spr "lexical error\n\nat %s" (strPos ()))
      | Failure s when Utils.strPrefix s "Lex: bad char" ->
          Log.printParseErr (spr "%s\n\nat %s" s (strPos ()))
      | Failure s when Utils.strPrefix s "parse error" ->
          Log.printParseErr s
      | Failure s when Utils.strPrefix s "lexical error" ->
          Log.printParseErr s
      | Lang.Parse_error(s) ->
          Log.printParseErr (spr "at %s\n\n%s" (strPos ()) s)
      | Parsing.Parse_error _  (* thrown when using ocamlyacc *)
      | LangParser.Error ->    (* thrown when using menhir *)
          Log.printParseErr
            (spr "unexpected token [%s]\n\nat %s" (lexeme lexbuf) (strPos ()))

let parseJStoEJS f =
  Exprjs_syntax.from_javascript
    (JavaScript.parse_javascript_from_channel (open_in f) f)

let doParseJavaScript f =
  LangUtils.sLoaded f (Desugar.desugar (parseJStoEJS f))

let doParseImpScript f =
  LangUtils.sLoaded f (doParse LangParser.program f)


(***** Main *******************************************************************)

let rec addPrelude prelude prog =
  match prelude.Lang.stmt with
    | Lang.SExternVal(x,t,s) ->
        LangUtils.wrapStmt (Lang.SExternVal (x, t, addPrelude s prog))
    | Lang.SLoadedSrc(f,s) ->
        LangUtils.wrapStmt (Lang.SLoadedSrc (f, addPrelude s prog))
    | Lang.SExp _ -> prog
    | _ -> failwith (Printer.strStmtAst prelude)

let runTc prog f =
  let prog = Typing.typecheck prog in
  Log.log1 "\n%s\n" (Utils.greenString "TC + CASTS: OK");
  Printer.printStmt prog f;
  (* sanity check that casts are sufficient *)
  Settings.castInsertionMode := false;
  ignore (Typing.typecheck prog);
  Log.log1 "\n%s\n" (Utils.greenString "TC: OK");
  () 

let _ =
  Arg.parse argSpecs anonArgFun usage;
  let (prog,fPrefix,jsMode) =
    match !srcFiles with
      | [ ] ->
          (LangUtils.sExp (LangUtils.eStr "no source file"), "out/dummy", true)
      | [f] ->
          begin match stripSuffix f ".js", stripSuffix f ".is" with
            | Some(fPrefix), _ -> (doParseJavaScript f, fPrefix, true)
            | _, Some(fPrefix) -> (doParseImpScript f, fPrefix, false)
            | _ -> (Log.log1 "%sBad file suffix\n" usage; Log.terminate ())
          end
      | _ -> (Log.log1 "%s" usage; Log.terminate ())
  in
  if !Settings.parseOnly then begin
    Log.log1 "\n%s\n" (Utils.greenString "PARSE: OK");
    exit 0
  end;
  let prog = LangUtils.removeUndefs prog in
  if jsMode then begin
    let prelude = doParseImpScript Settings.prims_file in
    let prog = addPrelude prelude prog in
    Log.log1 "\n%s\n" (Utils.greenString "DESUGARING: OK");
    Printer.printStmt prog (spr "%s%s" fPrefix ".is");
    runTc prog (spr "%s.1.is" fPrefix);
  end else begin
    match stripNumericSuffix fPrefix with
      | Some(fPrefix,n) -> runTc prog (spr "%s.%d.is" fPrefix (succ n))
      | None -> (Log.log1 "%s" usage; Log.terminate ())
  end;
  ()

