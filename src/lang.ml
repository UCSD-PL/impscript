
type var = string

type field = string

type width = ExactDomain | UnknownDomain

type loc =
  | LConst of var
  | LVar of var

type base_type =
  | TInt
  | TNum
  | TBool
  | TStr
  | TUndef
  | TNull

type typ =
  | TBase of base_type
  | TArrow of typ list * typ
  | TUnion of typ list
  | TAny
  | TBot
  | TRefMu of mu_type
  | TRefLoc of loc

and recd_type =
  | TRecd of width * (field * typ) list

and mu_type = var * recd_type

module RelySet =
  Set.Make (struct type t = (var * typ) let compare = compare end)

type rely = RelySet.t

type pre_type =
  | Typ of typ
  | OpenArrow of rely * typ list * typ
  | Exists of var * pre_type

type base_val =
  | VNum of float
  | VBool of bool
  | VStr of string
  | VUndef
  | VNull

type exp_ =
  | EBase of base_val
  | EVarRead of var
  | EFun of var list * stmt
  | EApp of exp * exp list
  | EObj of (field * exp) list
  | EObjRead of exp * exp
  | EFold of mu_type * exp
  | EUnfold of mu_type * exp
  | EAs of exp * pre_type
  | ECast of typ * typ
  | ETcErr of string * exp * stmt option (* stmt option for backtracking *)
  | ETcInsert of exp

and stmt_ =
  | SExp of exp
  | SVarDecl of var * stmt
  | SVarAssign of var * exp
  | SObjAssign of exp * exp * exp
  | SReturn of exp
  | SSeq of stmt * stmt 
  | SIf of exp * stmt * stmt
  | SWhile of exp * stmt
  | SVarInvariant of var * typ * stmt
  | SClose of var list * stmt
  | SLoadedSrc of string * stmt
  | SExternVal of var * typ * stmt
  | STcInsert of stmt

and exp = { exp: exp_ }
and stmt = { stmt: stmt_ }

exception Parse_error of string

let pr  = Printf.printf
let spr = Printf.sprintf
let fpr = Printf.fprintf

module VarMap = Map.Make (struct type t = var let compare = compare end)
module LocMap = Map.Make (struct type t = loc let compare = compare end)
module Vars   = Set.Make (struct type t = var let compare = compare end)
module Types  = Set.Make (struct type t = typ let compare = compare end)

