import Equivalence
import Blaster

open Equivalence

namespace Tests.Equivalence.Factorial

open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term (Term Const)

#import_uplc factorialLeft PlutusV3 single_cbor_hex "equivalence/examples/factorial/Scalus_0.12.1_Unisay.cbor_hex"
#import_uplc factorialRight PlutusV3 single_cbor_hex "equivalence/examples/factorial/Scalus_0.16.0_Unisay.cbor_hex"

def integerArgs (n : Integer) : List Term := [.Const (.Integer n)]

-- Keep execution limits independent. Blaster optimizes these runs during checking.
-- #prep_uplc uses the upstream runner, which conflates exhaustion with errors.
def factorialLeftRun (n : Integer) := execute factorialLeft.script (integerArgs n) 1000
def factorialRightRun (n : Integer) := execute factorialRight.script (integerArgs n) 1500

/-- Related inputs have the same integer meaning. The first prototype covers a
    stated domain; this is not a claim about all integer inputs. -/
def Inputs (x y : Integer) : Prop := x = y ∧ -5 ≤ x ∧ x ≤ 5

theorem checked : ∀ x y, Inputs x y →
    RunsEquivalent IntegerValues (factorialLeftRun x) (factorialRightRun y) := by
  blaster

theorem equivalent : Equivalent Inputs integerArgs integerArgs IntegerValues
    factorialLeft factorialRight :=
  equivalent_of_runs Inputs integerArgs integerArgs IntegerValues
    factorialLeft factorialRight 1000 1500 checked

-- Concrete diagnostics complement the symbolic check; they do not prove a domain.
#eval ([-5, 0, 1, 2, 5] : List Integer).map fun n =>
  (n, compareRuns integerValues (factorialLeftRun n) (factorialRightRun n))

-- Negative control: accidentally shifting the second script's argument must fail.
#blaster (gen-cex: 0) (solve-result: 1) [∀ x y, Inputs x y →
  ¬ RunsMismatch IntegerValues (factorialLeftRun x) (factorialRightRun (y + 1))]

-- Exercise the concrete checker against real UPLC executions.
example : compareRuns integerValues
    (factorialLeftRun 3) (factorialRightRun 2) = .inequivalent := by
  native_decide

example : compareRuns integerValues
    (factorialLeftRun 3)
    (execute factorialRight.script (integerArgs 3) 0) = .inconclusive := by
  native_decide

example : compareRuns integerValues
    (execute factorialLeft.script (integerArgs 3) 0)
    (execute factorialRight.script (integerArgs 3) 0) = .inconclusive := by
  native_decide

example : compareRuns integerValues
    (execute factorialLeft.script [.Error] 1000)
    (execute factorialRight.script [.Error] 1500) = .equivalent := by
  native_decide

example : compareRuns integerValues
    (factorialLeftRun 3)
    (execute factorialRight.script [.Error] 1500) = .inequivalent := by
  native_decide

-- Different representations: the second input stores n + 1, decoded before applying UPLC.
def offsetArgs (encoded : Integer) : List Term := integerArgs (encoded - 1)

theorem offset_encoding_equivalent :
    Equivalent (fun x y => Inputs x (y - 1)) integerArgs offsetArgs IntegerValues
      factorialLeft factorialRight := by
  apply equivalent_of_runs _ integerArgs offsetArgs IntegerValues
    factorialLeft factorialRight 1000 1500
  intro x y h
  exact checked x (y - 1) h

end Tests.Equivalence.Factorial
