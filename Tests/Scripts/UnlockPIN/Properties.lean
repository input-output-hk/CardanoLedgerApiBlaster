import CardanoLedgerApi.V3
import Tests.Scripts.UnlockPIN.UnlockPIN
import Blaster

namespace Tests.Scripts.UnlockPIN
open CardanoLedgerApi.V3
open PlutusCore.UPLC.Utils
open PlutusCore.Data (Data)


set_option warn.sorry false

def isVoidDatum (input : ScriptContext) : Prop :=
  match input.scriptContextScriptInfo with
  | .SpendingScript _ (some (.Constr 0 [])) => True
  | _ => False

def isExpectedRedeemer (input : ScriptContext) : Prop :=
  match input.scriptContextRedeemer with
  | .Constr 0 [.I 6781988 ] => True
  | _ => False

def isUnsafeRedeemer (input : ScriptContext) : Prop :=
  match input.scriptContextRedeemer with
  | .Constr _ [.I _ ] => True
  | _ => False

/-- The acceptance condition holds even without ledger-validity assumptions. -/
theorem successful_iff_expected_data :
  ∀ (input : ScriptContext),
    isSuccessful (appliedUnlockPIN.prop input) ↔ isExpectedRedeemer input ∧ isVoidDatum input := by blaster

/-- unlockPIN successful ↔ expected redeemer ∧ datum is void -/
theorem successful_iff_valid_pin_and_void_datum :
  ∀ (input : ScriptContext),
    validSpendingContext input →
    ( isSuccessful (appliedUnlockPIN.prop input) ↔ isExpectedRedeemer input ∧ isVoidDatum input ) := by
  intro input _
  exact successful_iff_expected_data input

-- This claim is refuted below using a valid context with PIN 0.
def unsafe_pin_imp_successful : Prop :=
  ∀ (input : ScriptContext),
    validSpendingContext input →
    isUnsafeRedeemer input →
    isVoidDatum input →
    isSuccessful (appliedUnlockPIN.prop input)

-- This claim is refuted below using a valid context with the correct PIN.
def cannot_break_pin : Prop :=
  ∀ (input : ScriptContext),
    validSpendingContext input →
    ¬ isSuccessful (appliedUnlockPIN.prop input)

/-- A balanced transaction with a script input, inline void datum, and its redeemer.
    Fixing the transaction skeleton keeps the counterexamples independent of SMT
    search through arbitrary V3 transaction lists. -/
def witnessContext (redeemer : Data) : ScriptContext :=
  let ref : TxOutRef := ⟨"input", 0⟩
  let datum := Data.Constr 0 []
  let ada (n : PlutusCore.Integer.Integer) : Value :=
    [(Data.B "", Data.Map [(Data.B "", Data.I n)])]
  let txInfo : TxInfo :=
    { txInfoInputs := [⟨ref, ⟨⟨.ScriptCredential "pin", none⟩, ada 2, .OutputDatum datum, none⟩⟩]
    , txInfoReferenceInputs := []
    , txInfoOutputs := [⟨⟨.PubKeyCredential "recipient", none⟩, ada 1, .NoOutputDatum, none⟩]
    , txInfoFee := 1
    , txInfoMint := []
    , txInfoTxCerts := []
    , txInfoWdrl := []
    , txInfoValidRange := .Constr 0
        [.Constr 0 [.Constr 0 [], .Constr 1 []], .Constr 0 [.Constr 2 [], .Constr 1 []]]
    , txInfoSignatories := []
    , txInfoRedeemers := [(.Spending ref, redeemer)]
    , txInfoData := []
    , txInfoId := "transaction"
    , txInfoVotes := []
    , txInfoProposalProcedures := []
    , txInfoCurrentTreasuryAmount := .Constr 1 []
    , txInfoTreasuryDonation := .Constr 1 []
    }
  ⟨txInfo, redeemer, .SpendingScript ref (some datum)⟩

theorem wrong_pin_witness_valid :
    validSpendingContext (witnessContext (.Constr 0 [.I 0])) := by native_decide

theorem correct_pin_witness_valid :
    validSpendingContext (witnessContext (.Constr 0 [.I 6781988])) := by native_decide

/-- The original unsafe-PIN claim is refuted by PIN 0 in a valid transaction. -/
theorem unsafe_pin_refuted : ¬ unsafe_pin_imp_successful := by
  intro h
  have accepted := h (witnessContext (.Constr 0 [.I 0])) wrong_pin_witness_valid
    (by trivial) (by trivial)
  have expected := ((successful_iff_expected_data _).mp accepted).1
  exact expected

/-- The original always-fails claim is refuted by the correct PIN in a valid transaction. -/
theorem cannot_break_pin_refuted : ¬ cannot_break_pin := by
  intro h
  apply h (witnessContext (.Constr 0 [.I 6781988])) correct_pin_witness_valid
  exact (successful_iff_expected_data _).mpr ⟨by trivial, by trivial⟩

end Tests.Scripts.UnlockPIN
