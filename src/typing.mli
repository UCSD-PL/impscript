
open Lang

type more_outputs = { retTypes: Types.t; usedVars: Vars.t }

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

val coerce    : (exp * typ * typ) -> (exp, unit) result

val tcExp     : (type_env * heap_env * exp)
                  -> (exp, pre_typ * heap_env * more_outputs) result

val tcStmt    : (type_env * heap_env * stmt)
                  -> (stmt, pre_typ * heap_env * more_outputs) result

val tcCoerce  : (type_env * heap_env * exp * typ)
                  -> (exp, heap_env * more_outputs) result

val typecheck : stmt -> stmt

