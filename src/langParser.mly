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
  | PSTcInsert of parse_stmt
  | PSTyAbbrev of ty_abbrev * (ty_var list * mu_type)

and block = parse_stmt list

let rec stmtOfBlock : block -> stmt = function

  (* pair binding forms with their scopes... *)
  | PSVarDecl(x)::l -> sLetRef x (stmtOfBlock l)
  | PSVarInvariant(x,t)::l -> sInvar x t (stmtOfBlock l)
  | PSExternVal(x,t)::l -> sExtern x t (stmtOfBlock l)
  | PSClose(xs)::l -> sClose xs (stmtOfBlock l)
  | PSTyAbbrev(x,def)::l -> sTyDef x def (stmtOfBlock l)

  (* ... a couple simple cases ... *)
  | [] -> sSkip
  | PSTcInsert(s)::l -> sTcInsert (stmtOfBlock (s::l))

  (* ... and use sequences for the rest *)
  | PSExp(e)::l -> sSeq [sExp e; stmtOfBlock l]
  | PSVarAssign(x,e)::l -> sSeq [sAssign x e; stmtOfBlock l]
  | PSObjAssign(e1,e2,e3)::l -> sSeq [sSet e1 e2 e3; stmtOfBlock l]
  | PSReturn(e)::l -> sSeq [sRet e; stmtOfBlock l]
  | PSWhile(e,s)::l -> sSeq [sWhile e (stmtOfBlock s); stmtOfBlock l]
  | PSIf(e,s1,s2)::l ->
      let (s1,s2) = (stmtOfBlock s1, stmtOfBlock s2) in
      sSeq [sIf e s1 s2; stmtOfBlock l]

let arrowOf inputs outputs =
  let (allLocs,tArgs,h1) = inputs in
  let (someLocs,tRet,h2) = outputs in
  (allLocs, tArgs, h1, someLocs, tRet, h2)

%}

%token <int> INT
%token <float> NUM
%token <string> STR
%token <bool> (* BOOL *) VBOOL
%token <Lang.var> VAR
%token <Lang.base_type> TBASE
%token <string> TVAR
%token <string> LVAR
%token
  EOF NULL UNDEF
  IF ELSE COMMA COLON LBRACE RBRACE SEMI LPAREN RPAREN LBRACK RBRACK LT GT
  PIPE FUN RET LETREF EQ EQARROW AS ARROW WHILE DOT QMARK TYPE
  EXTERN VAL INVARIANT CLOSE FOLD UNFOLD
  TANY TBOT REF DOTS MU STAR SLASH

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
 | EXTERN VAL x=VAR COLON t=typ SEMI { PSExternVal (x,t) }
 | INVARIANT x=VAR COLON t=typ SEMI { PSVarInvariant (x,t) }
 | CLOSE LBRACE xs=separated_list(COMMA,VAR) RBRACE SEMI { PSClose xs }
 | LBRACK ps=parse_stmt RBRACK { PSTcInsert ps }
 | TYPE x=VAR EQ mu=mu_type_def SEMI { PSTyAbbrev (x, ([], mu)) }
 | TYPE x=VAR LPAREN ys=separated_list(COMMA,TVAR) RPAREN
   EQ mu=mu_type_def SEMI { PSTyAbbrev (x, (ys, mu)) }

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
 | LPAREN s=typ EQARROW t=typ RPAREN   { (eCast s t).exp }
 | LPAREN arrow=poly_arrow_cast RPAREN { ECast arrow }
 | e=exp AS LPAREN t=typ RPAREN        { EAs (e, Typ t) }

 | e=exp LPAREN es=separated_list(COMMA,exp) RPAREN { EApp (e, es) }
 | LBRACE l=separated_list(COMMA,field_exp) RBRACE  { EObj l }
 | e=exp DOT f=VAR                                  { EObjRead (e, eStr f) }
 | e1=exp LBRACK e2=exp RBRACK                      { EObjRead (e1, e2) }
 | FOLD LPAREN mu=mu_type COMMA e=exp RPAREN        { EFold (mu, e) }
 | UNFOLD LPAREN mu=mu_type COMMA e=exp RPAREN      { EUnfold (mu, e) }

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

 | FUN LBRACK allLocs=separated_list(COMMA,LVAR) RBRACK
   LPAREN xts=separated_list(COMMA,annotated_formal) RPAREN SLASH h1=heap
   tRet=func_ret_type SLASH h2=heap LBRACE b=block RBRACE
     { let (xs,tArgs) = List.split xts in
       let arrow = Typ (TArrow (allLocs, tArgs, h1, [], tRet, h2)) in
       EAs (eFun xs (stmtOfBlock b), arrow) }

 | LBRACK e=exp_ RBRACK { ETcInsert (wrapExp e) }

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
 | NULL    { tNull }

 | LPAREN ts=separated_list(COMMA,typ) RPAREN ARROW s=typ { pureArrow ts s }
 | arrow=poly_arrow_type                                  { TArrow arrow }

 | LPAREN s=typ PIPE ts=separated_list(PIPE,typ) RPAREN { tUnion (s::ts) }
     (* conflicts for union types without parens... *)

 | x=TVAR                         { TExistsRef ("L", MuVar x) }

 | REF LPAREN l=loc RPAREN        { TRefLoc l }
 | LT l=loc GT                    { TRefLoc l }
 | STAR l=loc                     { TRefLoc l }

 | QMARK LPAREN t=typ RPAREN      { TMaybe t }

mu_type : 
 | m=mu_type_def                                    { m }
 | x=VAR                                            { MuAbbrev (x, []) }
 | x=VAR LPAREN ts=separated_list(COMMA,typ) RPAREN { MuAbbrev (x, ts) }

mu_type_def :
 | x=mu_binder rt=recd_type { Mu (x, rt) }

recd_type :
 | LBRACE fts=separated_list(COMMA,field_type) RBRACE
     { let (width,fts) =
         if fts = [] then (ExactDomain, fts)
         else match List.rev fts with
           | ("...",_)::fts -> (UnknownDomain, fts)
           | _              -> (ExactDomain, fts)
       in
       let l = List.filter (fun (f,_) -> f = "...") fts in
       if List.length l > 0 then Log.printParseErr "[...] must appear at end";
       TRecd (width, fts) }

field_exp :
 | f=VAR EQ e=exp { (f, e) }

field_type :
 | f=VAR COLON t=typ { (f, t) }
 | DOTS              { ("...", TBot) }

mu_binder :
 | MU x=TVAR DOT { x }

loc :
 | x=LVAR { LVar x }
 (* TODO loc constants *)

heap :
 | LPAREN h=separated_list(COMMA,heap_binding) RPAREN { h }

heap_binding :
 | STAR l=loc COLON mu=mu_type     { (l, HMu mu) }
 | STAR l=loc COLON rt=recd_type   { (l, HRecd rt) }

poly_arrow_type :
 | x=poly_arrow_inputs ARROW y=poly_arrow_outputs { arrowOf x y }

poly_arrow_cast :
 | x=poly_arrow_inputs EQARROW y=poly_arrow_outputs { arrowOf x y }

poly_arrow_inputs :
 | LBRACK allLocs=separated_list(COMMA,LVAR) RBRACK
   LPAREN tArgs=separated_list(COMMA,typ) RPAREN
   ho=option(slash_heap)
     { let h1 = match ho with None -> [] | Some h -> h in
       (allLocs, tArgs, h1) }

poly_arrow_outputs :
 | t=typ { ([], t, []) }

slash_heap :
 | SLASH h=heap { h }

exp : e=exp_ { wrapExp e } (* TODO attach line info here... *)

%%
