import Equivalence.ContextSyntax
import Equivalence.Ledger

/-!
Builds raw Plutus Data encodings for V3 spending contexts and transaction fields.
Provides address, value, interval, input and output constructors for context profiles.
Unpacks the shared spending frame and supplies a concrete ledger-model-valid example.
-/

namespace Equivalence.Context

open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.UPLC.Term (Term Program)

def pubKeyAddress (key : ByteString) : Data :=
  .Constr 0 [.Constr 0 [.B key], .Constr 1 []]

def scriptAddress (hash : ByteString) : Data :=
  .Constr 0 [.Constr 1 [.B hash], .Constr 1 []]

def outputReference (txId : ByteString) (index : Int := 0) : Data :=
  .Constr 0 [.B txId, .I index]

/-- V3 output encoding; values and reference scripts retain arbitrary raw Data.
    A supplied datum is inline; absence uses the no-datum constructor. -/
def txOutput (address value : Data) (datum : Option Data := none)
    (referenceScript : Data := .Constr 1 []) : Data :=
  .Constr 0 [address, value, match datum with
    | some d => .Constr 2 [d]
    | none => .Constr 0 [], referenceScript]

def txInput (reference output : Data) : Data := .Constr 0 [reference, output]

def lovelace (quantity : Int) : Data := .Map [(.B "", .Map [(.B "", .I quantity)])]

/-- The unused redeemer entries form a tail after the current spending entry.
    Validity auditing checks uniqueness and ordering of the resulting map. -/
def withSpendingRedeemer (reference redeemer txInfo : Data) : Data :=
  match txInfo with
  | .Constr tag fields => .Constr tag (fields.modify 9 fun entries =>
      match entries with
      | .Map entries =>
        let purpose := Data.Constr 1 [reference]
        .Map ((purpose, redeemer) :: entries)
      | other => other)
  | other => other

/-- V3 spending ScriptContext, with a present spending datum. -/
def spendingContext (txInfo redeemer reference datum : Data) : Data :=
  .Constr 0 [withSpendingRedeemer reference redeemer txInfo, redeemer,
    .Constr 1 [reference, .Constr 0 [datum]]]

/-- Ledger-shaped finite, inclusive lower and exclusive upper interval bounds. -/
def range (lower upper : Int) : Data := .Constr 0 [
  .Constr 0 [.Constr 1 [.I lower], .Constr 1 []],
  .Constr 0 [.Constr 1 [.I upper], .Constr 0 []]]

/-- Unrestricted unused fields for raw-context exploration. Defaults reproduce
    the minimal context; arbitrary Data need not have ledger encodings. -/
structure RawUnusedTxInfo where
  referenceInputs : Data := .List []
  outputs : Data := .List []
  fee : Data := .I 0
  mint : Data := .Map []
  certificates : Data := .List []
  withdrawals : Data := .Map []
  redeemers : Data := .Map []
  datums : Data := .Map []
  txId : Data := .B "tx"
  votes : Data := .Map []
  proposals : Data := .List []
  treasury : Data := .Constr 1 []
  donation : Data := .Constr 1 []

/-- V3 TxInfo field order shared by the context domains. -/
def RawUnusedTxInfo.txInfo (unused : RawUnusedTxInfo) (inputs signatories : List Data)
    (lower upper : Int) : Data :=
  context_tx_info% unused inputs unused.outputs signatories (range lower upper)

/-- Common decoded frame for the structured V3 spending profiles.
    Profile-specific input/output shapes and bounds are checked separately. -/
structure SpendingFrame where
  inputs : List Data
  outputs : List Data
  signers : List Data
  validRange : Data
  reference : Data
  datum : Data
  redeemer : Data
  unused : RawUnusedTxInfo

/-- Decode the shared outer encoding and undo the current spending redeemer
    prefix. Preserve malformed non-map fields, as spendingContext does. -/
def unpackSpendingContext : Data → Option SpendingFrame
  | .Constr 0 [.Constr 0 [.List inputs, referenceInputs, .List outputs, fee, mint,
      certificates, withdrawals, validRange, .List signers, redeemers, datums,
      txId, votes, proposals, treasury, donation], redeemer,
      .Constr 1 [reference, .Constr 0 [datum]]] => do
    let redeemers ← match redeemers with
      | .Map ((purpose, value) :: rest) =>
        if purpose == .Constr 1 [reference] && value == redeemer then some (.Map rest) else none
      | .Map [] => none
      | raw => some raw
    return {
      inputs := inputs, outputs := outputs, signers := signers, validRange := validRange
      reference := reference, datum := datum, redeemer := redeemer
      unused := {
        referenceInputs := referenceInputs, fee := fee, mint := mint
        certificates := certificates, withdrawals := withdrawals, redeemers := redeemers
        datums := datums, txId := txId, votes := votes, proposals := proposals
        treasury := treasury, donation := donation } }
  | _ => none

/-- One concrete member of the generic valid-context domain. These choices
    witness nonemptiness; they impose no restrictions on the symbolic domain. -/
def genericValidContext : Data :=
  let reference := outputReference ⟨String.mk (List.replicate 32 'r')⟩
  let address := scriptAddress ⟨String.mk (List.replicate 28 's')⟩
  let receiver := pubKeyAddress ⟨String.mk (List.replicate 28 'p')⟩
  let input := txInput reference (txOutput address (lovelace 10000000) (some (.I 0)))
  let output := txOutput receiver (lovelace 9999999)
  let tx := ({ fee := .I 1, outputs := .List [output] } : RawUnusedTxInfo).txInfo
    [input] [] 0 3000000
  spendingContext tx (.Constr 0 []) reference (.I 0)

def setField (value : Data) (index : Nat) (field : Data) : Data :=
  match value with
  | .Constr tag fields => .Constr tag (fields.set index field)
  | other => other

end Equivalence.Context
