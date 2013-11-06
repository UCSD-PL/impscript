{
open LangParser
}

let letter  = ['A'-'Z''a'-'z''_']
let digit   = ['0'-'9']
let ident   = ['a'-'z''_''&'] (letter|digit|''')*
(* let ident   = ['a'-'z''_''&'] (letter|digit|'''|'.')* *)
(* let tyvar   = ['A'-'Z'] (letter|digit)* *)
let tyvar   = ['''] (letter|digit)*
let white   = [' ' '\t' '\r']
let newline = ['\n']

let str =
  (letter
    | digit
    | [' ' '+' '-' '*' '/' '=' '(' ')' '&' '|' '.' ',' '{' '}' ':' ';' '#'])*


rule token = parse
  | eof { EOF }

  | "int"        { TBASE Lang.TInt }
  | "num"        { TBASE Lang.TNum }
  | "bool"       { TBASE Lang.TBool }
  | "str"        { TBASE Lang.TStr }
  | "any"        { TANY }
  | "bot"        { TBOT }
  | "ref"        { REF }
  | "mu"         { MU }

  | "true"         { VBOOL true }
  | "false"        { VBOOL false }
  | "var"          { LETREF }
  | "val"          { VAL }
  | "=>"           { EQARROW }
  | "="            { EQ }
  | "as"           { AS }
  | "->"           { ARROW }
  | "function"     { FUN }
  | "return"       { RET }
  | "while"        { WHILE }
  | "if"           { IF }
  | "else"         { ELSE }
  | "null"         { NULL }
  | "undefined"    { UNDEF }
  | "extern"       { EXTERN }
  | "invariant"    { INVARIANT }
  | "close"        { CLOSE }
  | "fold"         { FOLD }
  | "unfold"       { UNFOLD }
  | "..."          { DOTS }
  | "("            { LPAREN }
  | ")"            { RPAREN }
  | "{"            { LBRACE }
  | "}"            { RBRACE }
  | "["            { LBRACK }
  | "]"            { RBRACK }
  | "."            { DOT } (* NOTE: won't work with dots in idents *)
  | ","            { COMMA }
  | ";"            { SEMI }
  | ":"            { COLON }
  | "|"            { PIPE }

  | digit+ as s              { INT (int_of_string s) }
  | digit+ '.' digit* as s   { NUM (float_of_string s) }
  | ident as s               { VAR s } (* replace prime if going to Z3 *)
  | '"' (str as s) '"'       { STR s}
  (* | tyvar as s          { TVAR s } *)

  | white       { token lexbuf }
  | newline     { Lexing.new_line lexbuf; token lexbuf }

  | "(*"		    { comments 0 lexbuf }

  | _  { raise (Failure ("Lex: bad char ["^(Lexing.lexeme lexbuf)^"]")) }

and comments level = parse
  | "*)"	  { if level = 0 then token lexbuf else comments (level-1) lexbuf }
  | "(*"  	{ comments (level+1) lexbuf }
  | newline { Lexing.new_line lexbuf; comments level lexbuf }
  | _	  	  { comments level lexbuf }
  | eof		  { Printf.printf "comments are not closed\n"; raise End_of_file }

