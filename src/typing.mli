
open Lang

type more_outputs = { retTypes: Types.t; usedVars: Vars.t }

val sub       : (typ * typ) -> bool
val join      : typ -> typ -> typ
val coerce    : exp -> typ -> typ -> exp
val tcExp     : type_env -> heap_env -> exp
                -> (exp * pre_typ * heap_env * more_outputs)
val tcStmt    : type_env -> heap_env -> stmt
                -> (stmt * pre_typ * heap_env * more_outputs)
val tcCoerce  : type_env -> heap_env -> exp -> typ
                -> (exp * heap_env * more_outputs)

val typecheck : stmt -> stmt
