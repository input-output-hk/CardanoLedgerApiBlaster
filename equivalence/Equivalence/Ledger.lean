import CardanoLedgerApi.V3

/-!
Connects raw context Data to the existing V3 ledger model through IsData decoding.
Checks spending-context validity independently of application script acceptance.
Produces an audit of failed ledger checks for concrete witnesses and counterexamples.
-/

namespace Equivalence.Ledger

open CardanoLedgerApi.IsData.Class
open PlutusCore.Data (Data)
open PlutusCore.UPLC.Term (Term)

abbrev ScriptContext := CardanoLedgerApi.V3.Contexts.ScriptContext

def decode (raw : Data) : Option ScriptContext := IsData.fromData raw

def validContext (raw : Data) : Bool :=
  (decode raw).any CardanoLedgerApi.V3.Contexts.validSpendingContext

def validScriptContext (raw : Data) : Bool :=
  (decode raw).any CardanoLedgerApi.V3.Contexts.validScriptContext

def validArguments : List Term → Bool
  | [.Const (.Data raw)] => validContext raw
  | _ => false

/-- Diagnose the existing ledger model's rules, independently of whether the
    application validator accepts. This does not establish on-chain reachability. -/
def checks (raw : Data) (spendingOnly := true) : List (String × Bool) :=
  match decode raw with
  | none => [("context_encoding", false)]
  | some ctx =>
    let tx := ctx.scriptContextTxInfo
    let datumMatches := match ctx.scriptContextScriptInfo with
      | .SpendingScript _ datum =>
        (CardanoLedgerApi.V3.Contexts.findOwnInput ctx).any fun input =>
          CardanoLedgerApi.V3.Contexts.validInputDatum datum input.txInInfoResolved ctx
      | _ => true
    let purposeMatches := !spendingOnly || match ctx.scriptContextScriptInfo with
      | .SpendingScript .. => true
      | _ => false
    [("script_purpose", purposeMatches),
     ("spending_datum", datumMatches),
     ("script_info", CardanoLedgerApi.V3.Contexts.validScriptInfo ctx),
     ("inputs", CardanoLedgerApi.V3.Contexts.validInputs ctx),
     ("reference_inputs", CardanoLedgerApi.V3.Contexts.validReferenceInputs ctx),
     ("outputs", CardanoLedgerApi.V2.validOutputs tx.txInfoOutputs),
     ("positive_fee", tx.txInfoFee > 0),
     ("mint", CardanoLedgerApi.V3.Contexts.validMintValue tx.txInfoMint),
     ("withdrawals", CardanoLedgerApi.V3.Contexts.validWithdrawals tx.txInfoWdrl),
     ("validity_interval", CardanoLedgerApi.V2.validTxRange tx.txInfoValidRange),
     ("signatories", CardanoLedgerApi.V2.validSigners tx.txInfoSignatories),
     ("redeemer_map", CardanoLedgerApi.V3.Contexts.validRedeemerMap tx.txInfoRedeemers),
     ("datum_map", CardanoLedgerApi.V2.validDatumMap tx.txInfoData),
     ("votes", CardanoLedgerApi.V3.Contexts.validVoterMap tx.txInfoVotes),
     ("treasury", CardanoLedgerApi.V3.Contexts.validTreasuryAmount tx.txInfoCurrentTreasuryAmount),
     ("donation", CardanoLedgerApi.V3.Contexts.validTreasuryDonation tx.txInfoTreasuryDonation),
     ("value_balance", CardanoLedgerApi.V3.Contexts.isBalanced ctx)]

def audit (raw : Data) (spendingOnly := true) : Lean.Json :=
  Lean.Json.mkObj [
    ("predicate", Lean.toJson (if spendingOnly then "CardanoLedgerApi.V3.validSpendingContext"
      else "CardanoLedgerApi.V3.validScriptContext")),
    ("valid", Lean.toJson (if spendingOnly then validContext raw else validScriptContext raw)),
    ("failed_checks", Lean.toJson ((checks raw spendingOnly).filterMap fun (name, valid) =>
      if valid then none else some name))]

end Equivalence.Ledger
