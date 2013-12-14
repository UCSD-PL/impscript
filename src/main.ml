
open Lexing

let pr = Printf.printf
let spr = Printf.sprintf

let (|>) x f = f x

let discardPreviousOutputFile () = 
  let oc = open_out Settings.out_filename in
  Printf.fprintf oc "";
  close_out oc;
  Unix.unlink Settings.out_filename;
  ()


(***** Command-line options ***************************************************)

let srcFiles  = ref []

let usage =
    "\n"
  ^ "Usage: ./impscript [options] (file.js | file.is | file.n.is)\n"
  ^ "\n"
  ^ "  Input       Mode\n"
  ^ "  ---------   -----------------------------------------------\n"
  ^ "\n"
  ^ "  file.js     1) Desugar JavaScript to ImpScript file.0.is\n"
  ^ "              2) Type check and insert casts in file.1.is\n"
  ^ "              3) Type check file.1.is (sanity check)\n"
  ^ "\n"
  ^ "  file.n.is   1) Type check and insert casts in file.n+1.is\n"
  ^ "              2) Type check file.n+1.is (sanity check)\n"
  ^ "\n"
  ^ "  file.is     1) Type check file.is\n"
  ^ "\n"
  ^ "  Options\n"
  ^ "  -----------------------------------------------------------"

let argSpecs = [
(*
  ("-checkingMode", Arg.Unit (fun () -> Settings.castInsertionMode := false),
                 "     check program without inserting casts");
*)
]

let anonArgFun s =
  srcFiles := !srcFiles @ [s]


(***** Execution Modes ********************************************************)

let stripSuffix s suf =
  if Str.string_match (Str.regexp (spr "\\(.*\\)%s$" suf)) s 0
  then Some (Str.matched_group 1 s)
  else None

let stripNumericSuffix s =
  if Str.string_match (Str.regexp "\\(.*\\)[.]\\([0-9]+\\)$" ) s 0
  then Some (Str.matched_group 1 s, int_of_string (Str.matched_group 2 s))
  else None

type mode =
  | JavaScript of string                  (* file.js   *)
  | ImpScriptInsertCasts of string * int  (* file.n.js *)
  | ImpScriptCheckCasts of string         (* file.is   *)

let modeOf f =
  match stripSuffix f ".js" with
   | Some fPrefix -> Some (JavaScript fPrefix)
   | None ->
      (match stripSuffix f "._.is" with
        | Some fPrefix -> Some (ImpScriptInsertCasts (fPrefix, 99998))
        | None ->
           (match stripSuffix f ".is" with
             | Some fPrefix ->
                (match stripNumericSuffix fPrefix with
                  | Some(fPrefix,n) -> Some (ImpScriptInsertCasts (fPrefix, n))
                  | None -> Some (ImpScriptCheckCasts fPrefix))
             | None -> None))

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
  f |> parseJStoEJS
    |> Desugar.desugar
    |> LangUtils.sLoaded f
    |> LangUtils.removeUndefs

let doParseImpScript f =
  f |> doParse LangParser.program
    |> LangUtils.sLoaded f
    |> LangUtils.removeUndefs

let rec addPrelude prelude prog =
  match prelude.Lang.stmt with
    | Lang.SExternVal(x,t,s) -> LangUtils.sExtern x t (addPrelude s prog)
    | Lang.SLoadedSrc(f,s)   -> LangUtils.sLoaded f (addPrelude s prog)
    | Lang.SExp _            -> prog
    | _ -> failwith (spr "addPrelude\n%s" (Printer.strStmtAst prelude))


(***** Main *******************************************************************)

let tcCheckCasts prog f =
  Settings.castInsertionMode := false;
  match Typing.typecheck prog with
   | Typing.Ok (prog, _) -> begin
       AcePrinter.print prog (spr "%s.html" f);
       Log.log1 "\n%s\n" (Utils.greenString "TC: OK");
      end
   | Typing.Err(prog) -> begin
       Log.log1 "\n%s " (Utils.redString "TC: FAILED!");
       Printer.printStmt prog (spr "%s.error" f);
     end

let tcInsertCasts prog f =
  Settings.castInsertionMode := true;
  match Typing.typecheck prog with
   | Typing.Ok(prog',()) -> begin
       Log.log1 "\n%s\n" (Utils.greenString "TRANSLATION: OK");
       if true (* TODO compare prog and prog' for meaningful differences *)
       then Printer.printStmt prog' f;
       (* sanity check that the inserted casts are sufficient for typing *)
       tcCheckCasts prog' f;
     end
   | Typing.Err(prog) -> begin
       Log.log1 "\n%s " (Utils.redString "TRANSLATION: FAILED!");
       Printer.printStmt prog f;
     end

let parseAndProcessFile f = function
  | JavaScript(fPrefix) -> begin
      let prog = doParseJavaScript f in
      let prelude = doParseImpScript Settings.prims_file in
      let prog = addPrelude prelude prog in
      Log.log1 "\n%s\n" (Utils.greenString "DESUGARING: OK");
      Printer.printStmt prog (spr "%s.0.is" fPrefix);
      tcInsertCasts prog (spr "%s.1.is" fPrefix);
    end
  | ImpScriptInsertCasts(fPrefix,n) -> 
      let prog = doParseImpScript f in
      tcInsertCasts prog (spr "%s.%d.is" fPrefix (succ n))
  | ImpScriptCheckCasts _ ->
      let prog = doParseImpScript f in
      tcCheckCasts prog f

let _ =
  discardPreviousOutputFile ();
  Arg.parse argSpecs anonArgFun usage;
  match !srcFiles with
    | [ ] -> exit 0
    | [f] -> (match modeOf f with
                | Some(mode) -> parseAndProcessFile f mode
                | None -> (Log.log1 "%s\n\nBad file suffix\n" usage;
                           Log.terminate ()))
    | _   -> (Log.log1 "%s" usage; Log.terminate ())

