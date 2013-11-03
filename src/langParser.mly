%{
open Lang
open LangUtils

(* a slightly different version of the Lang.stmt type with no sequences
   and binding forms are not paired with their scopes *)
type parse_stmt = (* TODO attach line info *)
  | PSExp of exp
  | PSVarDecl of var
  | PSVarAssign of var * exp
  | PSObjAssign of exp * exp * exp
  | PSReturn of exp
  | PSIf of exp * block * block 
  | PSWhile of exp * block
  | PSVarInvariant of var * typ
  | PSClose of var list
  | PSExternVal of var * typ

and block = parse_stmt list

let rec stmtOfBlock : block -> stmt = function

  (* pair binding forms with their scopes... *)
  | PSVarDecl(x)::l -> sLetRef x (stmtOfBlock l)
  | PSVarInvariant(x,t)::l ->
      wrapStmt (SVarInvariant (x, t, stmtOfBlock l))
  | PSExternVal(x,t)::l ->
      wrapStmt (SExternVal (x, t, stmtOfBlock l))
  | PSClose(xs)::l ->
      wrapStmt (SClose (xs, stmtOfBlock l))

  (* ... and use sequences for the rest *)
  | [] -> sSkip
  | PSExp(e)::l -> sSeq [sExp e; stmtOfBlock l]
  | PSVarAssign(x,e)::l -> sSeq [sAssign x e; stmtOfBlock l]
  | PSObjAssign(e1,e2,e3)::l -> sSeq [sSet e1 e2 e3; stmtOfBlock l]
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
  IF ELSE COMMA COLON LBRACE RBRACE SEMI LPAREN RPAREN LBRACK RBRACK
  PIPE FUN RET LETREF EQ EQARROW AS ARROW WHILE DOT
  EXTERN VAL INVARIANT CLOSE
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
 | e1=exp DOT f=VAR EQ e3=exp SEMI             { PSObjAssign (e1, eStr f, e3) }
 | e1=exp LBRACK e2=exp RBRACK EQ e3=exp SEMI  { PSObjAssign (e1, e2, e3) }
 | IF LPAREN e=exp RPAREN LBRACE s1=block RBRACE
   ELSE LBRACE s2=block RBRACE  { PSIf (e,s1,s2) }
 | WHILE LPAREN e=exp RPAREN LBRACE s=block RBRACE { PSWhile(e,s) } 
 | EXTERN VAL x=VAR COLON t=typ { PSExternVal (x,t) }
 | LBRACK INVARIANT x=VAR COLON t=typ RBRACK { PSVarInvariant (x,t) }
 | LBRACK CLOSE LBRACE xs=separated_list(COMMA,VAR) RBRACE RBRACK
    { PSClose xs }

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
 | e=exp AS t=typ                      { EAs (e, Typ t) }

 | e=exp LPAREN es=separated_list(COMMA,exp) RPAREN { EApp (e, es) }
 | LBRACE l=separated_list(COMMA,field_exp) RBRACE  { EObj l }
 | e=exp DOT f=VAR                                  { EObjRead (e, eStr f) }
 | e1=exp LBRACK e2=exp RBRACK                      { EObjRead (e1, e2) }

 | FUN LPAREN xts=separated_list(COMMA,maybe_annotated_formal) RPAREN
     tRetOpt=option(func_ret_type)
     LBRACE b=block RBRACE
       { let (xs,tArgOpts) = List.split xts in
         match tRetOpt with
           | None -> EFun (xs, stmtOfBlock b)
           | Some(tRet) ->
               let tArgs =
                 List.map (function None -> TAny | Some(t) -> t) tArgOpts in
               EAs (eFun xs (stmtOfBlock b), ptArrow RelySet.empty tArgs tRet) }

 | FUN LBRACE r=separated_list(COMMA,annotated_formal) RBRACE
   LPAREN xts=separated_list(COMMA,annotated_formal) RPAREN
   tRet=func_ret_type LBRACE b=block RBRACE
     { let (xs,tArgs) = List.split xts in
       let h =
         List.fold_left
           (fun acc (x,t) -> RelySet.add (x,t) acc) RelySet.empty r in
       EAs (eFun xs (stmtOfBlock b), ptArrow h tArgs tRet) }

maybe_annotated_formal :
 | x=VAR COLON t=typ { (x, Some t) }
 | x=VAR             { (x, None) }

annotated_formal :
 | x=VAR COLON t=typ { (x, t) }

func_ret_type :
 | ARROW t=typ { t }

typ :
 | t=TBASE { TBase t }
 | TANY    { TAny }
 | TBOT    { TBot }
 | UNDEF   { tUndef }
 | LPAREN ts=separated_list(COMMA,typ) RPAREN ARROW s=typ { TArrow (ts, s) }
 | LPAREN s=typ PIPE ts=separated_list(PIPE,typ) RPAREN { tUnion (s::ts) }
     (* conflicts for union types without parens... *)

field_exp :
 | f=VAR EQ e=exp { (f, e) }

exp : e=exp_ { wrapExp e } (* TODO attach line info here... *)

%%
