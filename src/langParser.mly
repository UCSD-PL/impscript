%{
open Lang
open LangUtils

(* a slightly different version of the Lang.stmt type with no sequences
   and binding forms are not paired with their scopes *)
type parse_stmt = (* TODO attach line info *)
  | PSExp of exp
  | PSVarDecl of var
  | PSVarAssign of var * exp
  | PSReturn of exp
  | PSIf of exp * block * block 
  | PSWhile of exp * block
  | PSVarInvariant of var * typ
  | PSExternVal of var * typ

and block = parse_stmt list

let rec stmtOfBlock : block -> stmt = function

  (* pair binding forms with their scopes... *)
  | PSVarDecl(x)::l -> sLetRef x (stmtOfBlock l)
  | PSVarInvariant(x,t)::l ->
      wrapStmt (SVarInvariant (x, t, stmtOfBlock l))
  | PSExternVal(x,t)::l ->
      wrapStmt (SExternVal (x, t, stmtOfBlock l))

  (* ... and use sequences for the rest *)
  | [] -> sSkip
  | PSExp(e)::l -> sSeq [sExp e; stmtOfBlock l]
  | PSVarAssign(x,e)::l -> sSeq [sAssign x e; stmtOfBlock l]
  | PSReturn(e)::l -> sSeq [sRet e; stmtOfBlock l]
  | PSIf(e,s1,s2)::l ->
      let (s1,s2) = (stmtOfBlock s1, stmtOfBlock s2) in
      sSeq [sIf e s1 s2; stmtOfBlock l]
  | PSWhile(e,s)::l ->
      sSeq [sWhile e (stmtOfBlock s); stmtOfBlock l]

%}

%token <int> INT
%token <float> NUM
%token <string> STR
%token <bool> (* BOOL *) VBOOL
%token <Lang.var> VAR
%token <Lang.base_type> TBASE
(* %token <string> TVAR *)
%token
  EOF NULL UNDEF
  IF ELSE COMMA COLON LBRACE RBRACE SEMI LPAREN RPAREN
  PIPE FUN RET LETREF EQ EQARROW AS ARROW
  EXTERN VAL INVARIANT
  TANY TBOT

%type <Lang.stmt> program
%start program

%%

program : b=block EOF { stmtOfBlock b }

block : l=list(parse_stmt) { l }

parse_stmt :
 | e=exp SEMI           { PSExp e }
 | LETREF x=VAR SEMI    { PSVarDecl x }
 | x=VAR EQ e=exp SEMI  { PSVarAssign(x,e) }
 | RET e=exp SEMI       { PSReturn e }
 | IF LPAREN e=exp RPAREN LBRACE s1=block RBRACE
   ELSE LBRACE s2=block RBRACE  { PSIf (e,s1,s2) }
 | EXTERN VAL x=VAR COLON t=typ { PSExternVal (x,t) }
 | INVARIANT x=VAR COLON t=typ  { PSVarInvariant (x,t) }

base_val :
 | b=VBOOL { VBool b }
 | n=NUM   { VNum n }
 | i=INT   { VNum (float_of_int i) }
 | s=STR   { VStr s }
 | UNDEF   { VUndef }
 | NULL    { VNull }

exp_ :
 | v=base_val                          { EBase v }
 | x=VAR                               { EVarRead x }
 | LPAREN s=typ EQARROW t=typ RPAREN   { ECast (s, t) }
 | e=exp AS t=typ                      { EAs (e, t) }

 (* in cast insertion mode, throw away any casts that appeared in the source
    file, as these were inserted by the previous pass of cast insertion *)

 | e=exp LPAREN es=separated_list(COMMA,exp) RPAREN
     { match !Settings.castInsertionMode, e.exp, es with
         | true, ECast _, [e1] -> e1.exp
         | _                   -> EApp (e, es) }

 | FUN LPAREN xts=separated_list(COMMA,formal) RPAREN
     tRetOpt=option(func_ret_type)
     LBRACE b=block RBRACE
       { let (xs,tArgOpts) = List.split xts in
         match tRetOpt with
           | None -> EFun (xs, stmtOfBlock b)
           | Some(tRet) ->
               let tArgs =
                 List.map (function None -> TAny | Some(t) -> t) tArgOpts in
               EAs (eFun xs (stmtOfBlock b), TArrow (tArgs, tRet)) }

formal :
 | x=VAR COLON t=typ { (x, Some t) }
 | x=VAR             { (x, None) }

func_ret_type :
 | ARROW t=typ { t }

typ :
 | t=TBASE { TBase t }
 | TANY    { TAny }
 | TBOT    { TBot }
 | UNDEF   { tUndef }
 | LPAREN ts=separated_list(COMMA,typ) RPAREN ARROW s=typ { TArrow (ts, s) }
 | LPAREN s=typ PIPE t=typ RPAREN { TUnion [s;t] }
     (* conflicts for union types without parens... *)
     (* | s=typ PIPE t=typ { TUnion [s;t] } *)
     (* | LPAREN ts=separated_list(PIPE,typ) RPAREN { TUnion ts } *)

exp : e=exp_ { wrapExp e } (* TODO attach line info here... *)

%%
