
type var = string

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

module RelySet =
  Set.Make (struct type t = (var * typ) let compare = compare end)

type rely = RelySet.t

type pre_typ =
  | Typ of typ
  | OpenArrow of rely * typ list * typ

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
  | EAs of exp * pre_typ
  | ECast of typ * typ
  | ETcErr of string * exp

and stmt_ =
  | SExp of exp
  | SVarDecl of var * stmt
  | SVarAssign of var * exp
  | SReturn of exp
  | SSeq of stmt * stmt 
  | SIf of exp * stmt * stmt
  | SWhile of exp * stmt
  | SVarInvariant of var * typ * stmt
  | SClose of var list * stmt
  | SLoadedSrc of string * stmt
  | SExternVal of var * typ * stmt

and exp = { exp: exp_ }
and stmt = { stmt: stmt_ }

type type_env_binding =
  | Val of typ
  | StrongRef
  | InvariantRef of typ
  
module VarMap = Map.Make (struct type t = var let compare = compare end)

type type_env = type_env_binding VarMap.t

type heap_env = pre_typ VarMap.t

module Vars = Set.Make (struct type t = var let compare = compare end)

module Types = Set.Make (struct type t = typ let compare = compare end)

exception Parse_error of string

let pr  = Printf.printf
let spr = Printf.sprintf
let fpr = Printf.fprintf

