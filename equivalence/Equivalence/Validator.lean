import Equivalence.Function

namespace Equivalence.Validator

open Acceptance (Result)
open PlutusCore.UPLC.Term (Program Term)

/-- Bounded acceptance observes unfinished execution as nonacceptance within
    the declared limit. Strict acceptance retains the unknown result. -/
def observe (bounded : Bool) : Result → Result
  | .unfinished => if bounded then .budgetExhausted else .unfinished
  | result => result

def execute (program : Program) (args : List Term) (cpu memory : Nat) (v3 : Bool)
    (bounded := false) (budgeted := true) (steps := 100000) : Result :=
  observe bounded (Function.execute program args cpu memory v3 budgeted steps)

end Equivalence.Validator
