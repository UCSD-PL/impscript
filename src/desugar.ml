
open Lang
open LangUtils

module E = Exprjs_syntax
module J = JavaScript_syntax
module L = Lambdajs_syntax

module IdMap = Prelude.IdMap
module IdSet = Prelude.IdSet
module IdSetExt = Prelude.IdSetExt

module StrSet = Utils.StrSet


(***** Desugaring expressions *************************************************)

type env = { vars: unit IdMap.t; funcNum: int }

let emptyEnv = {
  funcNum = 0;
  vars = List.fold_left
           (fun acc x -> IdMap.add x () acc)
           IdMap.empty [];
}

let addVar x env = { env with vars = IdMap.add x () env.vars }

let funcCount = ref 0

let dsConst = function
  | J.CString(s) -> EBase (VStr s)
  | J.CNum(n)    -> EBase (VNum n)
  | J.CInt(i)    -> EBase (VNum (float_of_int i))
  | J.CBool(b)   -> EBase (VBool b)
  | J.CNull      -> EBase (VNull)
  | J.CUndefined -> EBase (VUndef)
  | J.CRegexp _  -> failwith "dsConst CRegexp"

let rec dsExp env e  = { exp = dsExp_ env e }

and dsStmt env s = { stmt = dsStmt_ env s }

and dsExp_ (env:env) = function

  | E.ConstExpr (_, c) -> dsConst c

  (**  x  *********************************************************************)
  | E.VarExpr (p, x) -> (eVar x).exp

  | E.IdExpr (p, x) -> failwith "ds_ id"
  | E.ObjectExpr (_, fes) -> failwith "ds_ object"
  | E.ArrayExpr (_, es) -> failwith "ds_ array"
  | E.NewExpr _ -> failwith "dsExp New"
  | E.ThisExpr p -> failwith "ds_ this"

  (**  e1[e2]  ****************************************************************)
  | E.BracketExpr (_, e1, e2) -> failwith "ds_ bracket"

  (**  op e  ******************************************************************)
  | E.PrefixExpr (_, "prefix:delete", E.BracketExpr (_, ed, ek)) ->
      failwith "ds_ prefix"
  | E.PrefixExpr (_, "prefix:delete", _) -> failwith "ds_ prefix"
  | E.PrefixExpr (_, op, e) ->
      let e0 =
        match op with
          | "prefix:typeof" -> "_typeof"
          | "prefix:!"      -> "_not"
          | "prefix:-"      -> "_uminus"
          | x               -> failwith (spr "Op1Prefix [%s]" x)
      in
      (eApp (eVar e0) [dsExp env e]).exp

  (**  e1 op e2  **************************************************************)
  | E.InfixExpr (_, "in", ek, ed) -> failwith "ds_ infix"
  | E.InfixExpr (p, "!=", e1, e2) -> failwith "ds_ infix"
  | E.InfixExpr (p, "!==", e1, e2) -> failwith "ds_ infix"
  | E.InfixExpr (_, op, e1, e2) ->
      let e0 =
        match op with
          | "+"   -> "_plus"
          | "-"   -> "_minus"
          | "*"   -> "_mult"
          | "/"   -> "_div"
          | "=="  -> "_eek"
          | "===" -> "_threek"
          | ">"   -> "_gt"
          | ">="  -> "_ge"
          | "<="  -> "_le"
          | "<"   -> "_lt"
          | "&&"  -> "_and"
          | "||"  -> "_or"
          | _     -> failwith (spr "Op2Infix [%s]" op)
      in
      (eApp (eVar e0) [dsExp env e1; dsExp env e2]).exp

  (**  f(args)  ***************************************************************)
  | E.AppExpr (p, f, args) -> EApp (dsExp env f, List.map (dsExp env) args)

  (**  function (args) { body }  **********************************************)
  | E.FuncExpr (_, args, body) ->
      let env = List.fold_left (fun acc x -> addVar x acc) env args in
      EFun (args, dsStmt env body)

  | _ -> failwith "dsExp match failure"

and dsStmt_ env e = match e with

  | E.ConstExpr _
  | E.VarExpr _
  | E.IdExpr _
  | E.ObjectExpr _
  | E.ArrayExpr _
  | E.ThisExpr _
  | E.BracketExpr _
  | E.PrefixExpr _
  | E.InfixExpr _
  | E.AppExpr _
  | E.FuncExpr _
  | E.NewExpr _ -> SExp (dsExp env e)

  (**  e1 = e2  ***************************************************************)
  | E.AssignExpr (_, E.VarLValue (_, x), e) -> SVarAssign (x, dsExp env e)

  (**  e1[e2] = e3  ***********************************************************)
  | E.AssignExpr (_, E.PropLValue (_, e1, e2), e3) -> failwith "ds_ assign"

  (**  let x = e1 in e2  ******************************************************)
  | E.LetExpr (_, x, e1, e2) -> failwith "ds_ let"

  (**  if (e1) { e2 } else { e3 } *********************************************)
  | E.IfExpr (_, e1, e2, e3) -> SIf (dsExp env e1, dsStmt env e2, dsStmt env e3)

  (**  var x = e1; e2  ********************************************************)
  | E.SeqExpr (_, E.VarDeclExpr (_, x, e1), e2) ->
      dsVarDecl env x (Some e1) e2

  (**  function f(args){ body }; e2  ******************************************)
  | E.SeqExpr (p0, E.FuncStmtExpr (p, f, args, body), e2) ->
      dsStmt_ env
        (E.SeqExpr (p0, E.VarDeclExpr (p, f, E.FuncExpr (p, args, body)), e2))

  (**  e1; e2  ****************************************************************)
  | E.SeqExpr (_, e1, e2) -> sSeq_ [dsStmt env e1; dsStmt env e2]

  (**  @return { e }  *********************************************************)
  | E.LabelledExpr (_, "%return", e) -> dsStmt_ env e

  (**  break @return e  *******************************************************)
  | E.BreakExpr (_, "%return", e) -> SReturn (dsExp env e)

  (**  @break { while (test) { @continue { body } } }  ************************)
  | E.LabelledExpr (_, "%break",
        E.WhileExpr (_, test, E.LabelledExpr (_, "%continue", body))) ->
      SWhile (dsExp env test, dsStmt env body)

  (**  @break { while (test) { @continue { body }; incr } }  ******************)
  | E.LabelledExpr (_, "%break",
        E.WhileExpr (_, test, E.SeqExpr (_,
            E.LabelledExpr(_, "%continue", body), incr))) ->
      SWhile (dsExp env test, sSeq [dsStmt env body; dsStmt env incr])

  | E.BreakExpr (_, bl, e) -> failwith (spr "break %s" bl)
  | E.WhileExpr _ -> failwith "dsStmt while"
  | E.DoWhileExpr _ -> failwith "dsStmt dowhole"
  | E.LabelledExpr (_, l, e) -> failwith (spr "dsStmt label [%s]" l)
  | E.ForInExpr _ -> failwith "dsStmt forin"
  | E.VarDeclExpr _ -> failwith "dsStmt vardecl"
  | E.TryCatchExpr _ -> failwith "dsStmt try"
  | E.TryFinallyExpr _ -> failwith "dsStmt try"
  | E.ThrowExpr _ -> failwith "dsStmt throw"
  | E.FuncStmtExpr _ -> failwith "dsStmt func"
  | E.HintExpr _ -> failwith "dsStmt hint"

and dsVarDecl env x xInit s =
  let s = dsStmt (addVar x env) s in
  match xInit with
    | None     -> SVarDecl (x, s)
    | Some(ex) -> SVarDecl (x, sSeq [sAssign x (dsExp env ex); s])

let desugar e =
  dsStmt emptyEnv e


(***** Sequencing EJS expressions *********************************************)

(* The JS LangParser2 doesn't have a "prelude" production, so this fakes it by
   stitching together e1 and e2 as if e1 were a prelude. Assumes that e1 is
   a sequence terminated by undefined. This is better than SeqExpr(e1,e2),
   which is no longer a flat top-level sequence. *)

let makeFlatSeq e1 e2 =
  let rec foo = function
    | E.SeqExpr (p, e, E.ConstExpr (_, J.CUndefined)) -> E.SeqExpr (p, e, e2)
    | E.SeqExpr (p, e1, e2) -> E.SeqExpr (p, e1, foo e2)
    | _ -> failwith "makeFlatSeq"
  in
  foo e1

