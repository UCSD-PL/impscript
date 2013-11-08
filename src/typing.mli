
open Lang

module TypeEnv : sig type t end
module HeapEnv : sig type t end
module MoreOut : sig type t end

type ('a, 'b) result =
  | Ok of 'a * 'b
  | Err of 'a

val run : ('c -> ('a, 'b) result)
           -> 'c
           -> ('a -> ('a, 'b) result)
           -> ('a -> 'b -> ('a, 'b) result)
           -> ('a, 'b) result

val sub       : (typ * typ) -> bool

val join      : typ -> typ -> typ

val coerce    : (exp * typ * typ) -> (exp, bool) result

val tcExp     : (TypeEnv.t * HeapEnv.t * exp)
                  -> (exp, pre_type * HeapEnv.t * MoreOut.t) result

val tcStmt    : (TypeEnv.t * HeapEnv.t * stmt)
                  -> (stmt, pre_type * HeapEnv.t * MoreOut.t) result

val tcCoerce  : (TypeEnv.t * HeapEnv.t * exp * typ)
                  -> (exp, HeapEnv.t * MoreOut.t) result

val typecheck : stmt -> (stmt, unit) result

