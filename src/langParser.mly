%{
open Lang
open LangUtils

(* a slightly different version of the Lang.stmt type with no sequences
   and binding forms are not paired with their scopes *)
type parse_stmt = (* TODO attach line info *)
  | PSExp of exp
  | PSVarDecl of var * exp option
  | PSVarAssign of var * exp
  | PSObjAssign of exp * exp * exp
  | PSReturn of exp
  | PSIf of exp * block * block 
  | PSWhile of exp * block
  | PSVarInvariant of var * typ
  | PSClose of var list
  | PSExternVal of var * typ
  | PSTcInsert of parse_stmt
  | PSMuAbbrev of ty_abbrev * (ty_var list * mu_type)
  | PSBlankLine

and block = parse_stmt list

let rec stmtOfBlock : block -> stmt = function

  (* pair binding forms with their scopes... *)
  | PSVarDecl(x,None)::l -> sLetRef x (stmtOfBlock l)
  | PSVarInvariant(x,t)::l -> sInvar x t (stmtOfBlock l)
  | PSExternVal(x,t)::l -> sExtern x t (stmtOfBlock l)
  | PSClose(xs)::l -> sClose xs (stmtOfBlock l)
  | PSMuAbbrev(x,def)::l -> sMuDef x def (stmtOfBlock l)

  (* ... a couple simple cases ... *)
  | [] -> sSkip
  | PSTcInsert(s)::l -> sTcInsert (stmtOfBlock (s::l))
  | PSVarDecl(x,Some(e))::l ->
      stmtOfBlock (PSVarDecl (x, None) :: PSVarAssign (x, e) :: l)

  (* ... and use sequences for the rest *)
  | PSExp(e)::l -> sSeq [sExp e; stmtOfBlock l]
  | PSVarAssign(x,e)::l -> sSeq [sAssign x e; stmtOfBlock l]
  | PSObjAssign(e1,e2,e3)::l -> sSeq [sSet e1 e2 e3; stmtOfBlock l]
  | PSReturn(e)::l -> sSeq [sRet e; stmtOfBlock l]
  | PSBlankLine::l -> sSeq [sBlankLine; stmtOfBlock l]
  | PSWhile(e,s)::l -> sSeq [sWhile e (stmtOfBlock s); stmtOfBlock l]
  | PSIf(e,s1,s2)::l ->
      let (s1,s2) = (stmtOfBlock s1, stmtOfBlock s2) in
      sSeq [sIf e s1 s2; stmtOfBlock l]

let withDefault default opt = match opt with None -> default | Some x -> x

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
  BLANKLINE
  EOF NULL UNDEF
  IF ELSE COMMA COLON LBRACE RBRACE SEMI LPAREN RPAREN LBRACK RBRACK LT GT
  (* PIPE *) FUN RET LET IN LETREF EQ EQARROW AS ARROW WHILE DOT QMARK TYPE
  EXTERN VAL INVARIANT CLOSE FOLD UNFOLD ALL SOME U
  TANY TBOT REF DOTS MU STAR SLASH

%type <Lang.stmt> program
%start program

%%

program : b=block EOF { stmtOfBlock b }

block : l=list(parse_stmt) { l }

parse_stmt :
 | BLANKLINE                    { PSBlankLine }
 | e=exp SEMI                   { PSExp e }
 | LETREF x=VAR SEMI            { PSVarDecl (x, None) }
 | LETREF x=VAR EQ e =exp SEMI  { PSVarDecl (x, Some e) }
 | x=VAR EQ e=exp SEMI          { PSVarAssign(x,e) }
 | RET e=exp SEMI               { PSReturn e }

 | e1=exp DOT f=VAR EQ e3=exp SEMI             { PSObjAssign (e1, eStr f, e3) }
 | e1=exp LBRACK e2=exp RBRACK EQ e3=exp SEMI  { PSObjAssign (e1, e2, e3) }

 | IF LPAREN e=exp RPAREN LBRACE s1=block RBRACE
   ELSE LBRACE s2=block RBRACE                     { PSIf (e,s1,s2) }
 | WHILE LPAREN e=exp RPAREN LBRACE s=block RBRACE { PSWhile(e,s) } 

 | EXTERN VAL x=VAR COLON t=typ SEMI { PSExternVal (x,t) }
 | INVARIANT x=VAR COLON t=typ SEMI { PSVarInvariant (x,t) }
 | CLOSE LBRACE xs=separated_list(COMMA,VAR) RBRACE SEMI { PSClose xs }
 | LBRACK ps=parse_stmt RBRACK { PSTcInsert ps }

 | TYPE x=VAR EQ mu=mu_type_def SEMI { PSMuAbbrev (x, ([], mu)) }
 | TYPE x=VAR LPAREN ys=separated_list(COMMA,TVAR) RPAREN
   EQ mu=mu_type_def SEMI { PSMuAbbrev (x, (ys, mu)) }

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
 | LPAREN arrow=arrow_cast RPAREN      { ECast arrow }
 | e=exp AS LPAREN t=typ RPAREN        { EAs (e, Typ t) }

 | e=exp LPAREN es=separated_list(COMMA,exp) RPAREN { EApp (e, es) }
 | LBRACE l=separated_list(COMMA,field_exp) RBRACE  { EObj l }
 | e=exp DOT f=VAR                                  { EObjRead (e, eStr f) }
 | e1=exp LBRACK e2=exp RBRACK                      { EObjRead (e1, e2) }
 | FOLD LPAREN mu=mu_type COMMA e=exp RPAREN        { EFold (mu, e) }
 | UNFOLD LPAREN mu=mu_type COMMA e=exp RPAREN      { EUnfold (mu, e) }
 | LBRACK e=exp_ RBRACK                             { ETcInsert (wrapExp e) }
 | LET x=VAR EQ e1=exp IN LPAREN e2=exp RPAREN      { ELet (x, e1, e2) }

 | FUN r=option(rely_set)
       f=option(VAR) iw=lambda_input_world
       ow=option(lambda_output_world) LBRACE b=block RBRACE

     { let (allLocs,xts,h1) = iw in
       let (xs,tArgs) = List.split xts in
       let isNone = function None -> true | _ -> false in
       match r, List.for_all isNone tArgs, allLocs, h1, ow with
         | None, true, None, None, None -> (* no annotations *)
             EFun (xs, stmtOfBlock b)
         | _ ->
             let r = withDefault RelySet.empty r in
             let allLocs = withDefault [] allLocs in
             let h1 = withDefault [] h1 in
             let tArgs = List.map (withDefault TAny) tArgs in
             let (someLocs,tRet,h2) =
               match ow with
                 | None -> ([], TAny, [])
                 | Some(someLocs,tRet,h2) ->
                     (withDefault [] someLocs, tRet, withDefault [] h2) in
             let arrow = ((allLocs, tArgs, h1), (someLocs, tRet, h2)) in
             let rely =
               match f, RelySet.is_empty r with
                 | None  , _     -> r
                 | Some f, true  -> RelySet.singleton (f, TArrow arrow)
                 | Some _, false ->
                     Log.printParseErr "bad recursive function annotation" in
             let ptArrow = finishArrow rely arrow in
             EAs (eFun xs (stmtOfBlock b), ptArrow) }

typ :
 | t=TBASE { TBase t }
 | TANY    { TAny }
 | TBOT    { TBot }
 | UNDEF   { tUndef }
 | NULL    { tNull }

 | arrow=arrow_type                    { TArrow arrow }
 | U LPAREN s=typ ts=list(typ) RPAREN  { tUnion (s::ts) }

 (* | LPAREN s=typ PIPE ts=separated_list(PIPE,typ) RPAREN { tUnion (s::ts) } *)

 (* TODO get rid of this *)
 | x=TVAR                         { TExistsRef ("L", MuVar x) }

 | REF LPAREN mu=mu_type RPAREN   { TExistsRef ("L", mu) }
 | REF LPAREN l=loc RPAREN        { TRefLoc l }
 | LT l=loc GT                    { TRefLoc l }
 | STAR l=loc                     { TRefLoc l }
 | QMARK LPAREN t=typ RPAREN      { TMaybe t }

mu_type : 
 | m=mu_type_def                                    { m }
 | x=TVAR                                           { MuVar x }
 | x=VAR                                            { MuAbbrev (x, []) }
 | x=VAR LPAREN ts=separated_list(COMMA,typ) RPAREN { MuAbbrev (x, ts) }

mu_type_def :
 | MU x=TVAR DOT rt=recd_type { Mu (x, rt) }

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

arrow_type :
 | LPAREN x=input_world RPAREN ARROW LPAREN y=output_world RPAREN { (x, y) }

arrow_cast :
 | x=input_world EQARROW y=output_world { (x, y) }

input_world :
 | ls=option(all_locs) ts=separated_list(COMMA,typ) h=option(slash_heap) 
     { (withDefault [] ls, ts, withDefault [] h) }

output_world :
 | ls=option(some_locs) t=typ h=option(slash_heap)
     { (withDefault [] ls, t, withDefault [] h) }

lambda_input_world :
 | LPAREN allLocs=option(all_locs)
          xts=separated_list(COMMA,maybe_annotated_formal)
          h1=option(slash_heap) RPAREN
     { (allLocs, xts, h1) }

lambda_output_world :
 | ARROW LPAREN someLocs=option(some_locs) tRet=typ h2=option(slash_heap) RPAREN
     { (someLocs, tRet, h2) }

maybe_annotated_formal :
 | x=VAR COLON t=typ { (x, Some t) }
 | x=VAR             { (x, None) }

annotated_formal :
 | x=VAR COLON t=typ { (x, t) }

rely_set :
 | LBRACE r=separated_list(COMMA,annotated_formal) RBRACE
     { List.fold_left
         (fun acc (x,t) -> RelySet.add (x,t) acc)
         RelySet.empty r }

all_locs  : ALL  l=separated_list(COMMA,LVAR) DOT { l }
some_locs : SOME l=separated_list(COMMA,LVAR) DOT { l }

loc :
 | x=LVAR { LVar x }
 (* TODO loc constants *)

slash_heap :
 | SLASH h=separated_list(COMMA,heap_binding) { h }

heap_binding :
 | STAR l=loc COLON mu=mu_type     { (l, HMu mu) }
 | STAR l=loc COLON rt=recd_type   { (l, HRecd rt) }

exp : e=exp_ { wrapExp e } (* TODO attach line info here... *)

%%
