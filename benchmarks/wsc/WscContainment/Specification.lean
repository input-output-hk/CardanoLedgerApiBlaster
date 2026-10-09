import WscContainment.Script

/-! Quantities, parameter decoding, and exemptions of the WSC containment
statement. These definitions preserve the original specification; no additional
input-size restriction is imposed. The proofs are opt-in tractability tests. -/

namespace WscContainment
open CardanoLedgerApi.V3
open CardanoLedgerApi.IsData.Class (IsData)
open PlutusCore.Data (Data)
open PlutusCore.UPLC.CekMachine (cekExecuteProgram)
open PlutusCore.UPLC.Utils (isSuccessful)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option stderrAsMessages false

namespace Containment

/-- Only the payment credential selects the programmable-token mini-ledger. -/
def paymentCredential (output : TxOut) : Credential :=
  output.txOutAddress.addressCredential

def outputQuantityAt (base : Credential) (currency : CurrencySymbol) (token : TokenName) :
    List TxOut → Int
  | [] => 0
  | output :: rest =>
      (if paymentCredential output == base then valueOf currency token output.txOutValue else 0) +
        outputQuantityAt base currency token rest

def inputQuantityAt (base : Credential) (currency : CurrencySymbol) (token : TokenName) :
    List TxInInfo → Int
  | [] => 0
  | input :: rest =>
      (if paymentCredential input.txInInfoResolved == base then
        valueOf currency token input.txInInfoResolved.txOutValue else 0) +
        inputQuantityAt base currency token rest

/-- The fifth redeemer field selects the protocol-parameters reference input. -/
def transferProtocolParametersIndex : Data → Option Int
  | .Constr 0 (_transferProofs :: _transferWithdrawals :: _ownerWithdrawals ::
      _mintProofs :: .I index :: _) => some index
  | _ => none

/-- Negative indices clamp to zero, as in the script's UPLC list operation. -/
def atIndex {α : Type} (index : Int) (values : List α) : Option α :=
  (values.drop index.toNat).head?

def protocolParameterFields : Data → Option (CurrencySymbol × Data)
  | .List (.B directory :: base :: _) => some (directory, base)
  | _ => none

/-- Decode the transaction-published parameters. Authentication is performed
    by the actual validator, not added as a premise here. -/
def parametersPublishedBy (ctx : ScriptContext) : Option (CurrencySymbol × Data) := do
  let index ← transferProtocolParametersIndex ctx.scriptContextRedeemer
  let reference ← atIndex index ctx.scriptContextTxInfo.txInfoReferenceInputs
  let datum ← txOutInlineDatum reference.txInInfoResolved
  protocolParameterFields datum

def hasFirstNonAdaCurrencySymbol (currency : CurrencySymbol) : Value → Bool
  | _adaEntry :: (.B candidate, _) :: _ => candidate == currency
  | _ => false

def directoryNodeInterval : Data → Option (CurrencySymbol × CurrencySymbol)
  | .List (.B key :: .B next :: _) => some (key, next)
  | _ => none

/-- This deliberately checks ALL reference inputs, not just the proof selected
    by the redeemer. This pre-existing conservative exemption can exclude more
    assets from the containment claim. -/
def hasCoveringDirectoryNode (directory currency : CurrencySymbol) : List TxInInfo → Bool
  | [] => false
  | reference :: rest =>
      let current :=
        match txOutInlineDatum reference.txInInfoResolved with
        | some datum =>
            match directoryNodeInterval datum with
            | some (key, next) =>
                decide (key < currency) && decide (currency < next) &&
                  hasFirstNonAdaCurrencySymbol directory reference.txInInfoResolved.txOutValue
            | none => false
        | none => false
      current || hasCoveringDirectoryNode directory currency rest

def isExempt (directory currency : CurrencySymbol) (references : List TxInInfo) : Bool :=
  (currency == adaSymbol) || hasCoveringDirectoryNode directory currency references

def isProgrammable (directory currency : CurrencySymbol) (references : List TxInInfo) : Bool :=
  !(isExempt directory currency references)

end Containment

end WscContainment
