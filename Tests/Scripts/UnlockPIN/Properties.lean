import CardanoLedgerApi.V2
import Tests.Scripts.UnlockPIN.UnlockPIN
import Blaster

namespace Tests.Scripts.UnlockPIN
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
  | .Constr 0 [.I 6781988 ] => True
  | _ => False

def isUnsafeRedeemer (input : SpendingInput) : Prop :=
  match input.redeemer with
  | .Constr _ [.I _ ] => True
  | _ => False

/-- unlockPIN successful ↔ expected redeemer ∧ datum is void -/
theorem successful_iff_valid_pin_and_void_datum :
  ∀ (input : SpendingInput),
    validSpendingContext input →
    ( isSuccessful (appliedUnlockPIN.prop input) ↔ isExpectedRedeemer input ∧ isVoidDatum input ) := by blaster

-- Counterexample expected expected if unlockPIN is successful when wrong redeemer is provided
def unsafe_pin_imp_successful : Prop :=
  ∀ (input : SpendingInput),
    validSpendingContext input →
    isUnsafeRedeemer input →
    isVoidDatum input →
    isSuccessful (appliedUnlockPIN.prop input)

#blaster (gen-cex: 0) (solve-result: 1) [unsafe_pin_imp_successful]

-- Counterexample expected: There exists at least one valid SpendingInput for which unlockPIN is successful.
def cannot_break_pin : Prop :=
  ∀ (input : SpendingInput),
    validSpendingContext input →
    ¬ isSuccessful (appliedUnlockPIN.prop input)

#blaster (gen-cex: 0) (solve-result: 1) [cannot_break_pin]

end Tests.Scripts.UnlockPIN
