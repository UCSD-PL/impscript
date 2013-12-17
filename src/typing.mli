
open Lang

module MoreOut : sig type t end

type ('a, 'b) result =
  | Ok of 'a * 'b
  | Err of 'a

val run : ('c -> ('a, 'b) result)
           -> 'c
           -> ('a -> ('a, 'b) result)
           -> ('a -> 'b -> ('a, 'b) result)
           -> ('a, 'b) result

val sub    : typ -> typ -> bool

val join   : typ -> typ -> typ

val coerce : (exp * typ * typ) -> (exp, bool) result

val tcExp
  : (type_env * heap_env * exp)
 -> (exp, pre_type * heap_env * MoreOut.t) result

val tcStmt
  : (type_env * heap_env * stmt)
 -> (stmt, pre_type * heap_env * MoreOut.t) result

val tcAndCoerce
  : (type_env * heap_env * exp * typ)
 -> (exp, heap_env * MoreOut.t) result

val typecheck : stmt -> (stmt, unit) result

