import CardanoLedgerApi.V2
import Tests.Scripts.HelloWorld.HelloWorld
import Blaster

namespace Tests.Scripts.HelloWorld
open CardanoLedgerApi.V2
open PlutusCore.UPLC.Utils
open PlutusCore.Data (Data)

set_option warn.sorry false

def isVoidDatum (input : SpendingInput) : Prop :=
  match input.datum with
  | .Constr 0 [] => True
  | _ => False

def isExpectedRedeemer (input : SpendingInput) : Prop :=
  match input.redeemer with
  | .Constr 0 [.B "Hello CTF!" ] => True
  | _ => False

def isUnsafeRedeemer (input : SpendingInput) : Prop :=
  match input.redeemer with
  | .Constr _ [.B _ ] => True
  | _ => False

/-- helloWorld successful ↔ expected redeemer ∧ datum is void -/
theorem successful_iff_valid_redeemer_and_void_datum :
  ∀ (input : SpendingInput),
   validSpendingContext input →
    (isSuccessful (appliedHelloWorld.prop input) ↔ isExpectedRedeemer input ∧ isVoidDatum input) := by blaster

-- Counterexample expected if helloWorld is successful when wrong redeemer is provided
def unsafe_redeemer_imp_successful : Prop :=
  ∀ (input : SpendingInput),
    validSpendingContext input →
    isUnsafeRedeemer input →
    isVoidDatum input →
    isSuccessful (appliedHelloWorld.prop input)

#blaster (gen-cex: 0) (solve-result: 1) [unsafe_redeemer_imp_successful]

-- Counterexample expected: There exists at least one valid SpendingInput for which helloWorld is successful.
def cannot_break_pwd : Prop :=
  ∀ (input : SpendingInput),
    validSpendingContext input → ¬ isSuccessful (appliedHelloWorld.prop input)

#blaster (gen-cex: 0) (solve-result: 1) [cannot_break_pwd]

end Tests.Scripts.HelloWorld
