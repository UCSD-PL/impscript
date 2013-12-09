
type var = string

type ty_abbrev = string

type loc_var = string

type ty_var = string

type field = string

type width = ExactDomain | UnknownDomain

type loc =
  | LConst of var
  | LVar of loc_var

type base_type =
  | TInt
  | TNum
  | TBool
  | TStr
  | TUndef
  | TNull

type typ =
  | TBase of base_type
  | TArrow of arrow
  | TUnion of typ list
  | TAny
  | TBot
  | TRefLoc of loc
  | TMaybe of typ
  | TExistsRef of loc_var * mu_type (* exists *L: 'x. Ref L *)

and arrow = input_world * output_world

and input_world  = (loc_var list * typ list * heap)
and output_world = (loc_var list * typ * heap)

and recd_type =
  | TRecd of width * (field * typ) list

and mu_type =
  | Mu of (ty_var * recd_type)
  | MuVar of ty_var
  | MuAbbrev of ty_abbrev * typ list

and loc_binding =
  | HRecd of recd_type
  | HMu of mu_type

and heap = (loc * loc_binding) list

module RelySet =
  Set.Make (struct type t = (var * typ) let compare = compare end)

type rely = RelySet.t

type pre_type =
  | Typ of typ
  | OpenArrow of rely * arrow
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
  | ECast of arrow
  | ETcErr of string * exp * stmt option (* stmt option for backtracking *)
  | ETcInsert of exp
  | ELet of var * exp * exp

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
  | SMuAbbrev of ty_abbrev * (ty_var list * mu_type) * stmt
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

