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

def spendingRedeemerEntry (reference redeemer : Data) : Data × Data :=
  (.Constr 1 [reference], redeemer)

def mintingContext (txInfo redeemer : Data) (currencySymbol : ByteString) : Data :=
  let purpose := Data.Constr 0 [.B currencySymbol]
  let tx := match txInfo with
    | .Constr tag fields => .Constr tag (fields.set 9 (.Map [(purpose, redeemer)]))
    | other => other
  .Constr 0 [tx, redeemer, purpose]

def mintValue (currencySymbol token : ByteString) (quantity : Int) : Data :=
  .Map [(.B currencySymbol, .Map [(.B token, .I quantity)])]

/-- Add entries before the current spending entry in an encoded context. -/
def prependEarlierRedeemers (raw : Data) (earlier : List (Data × Data)) : Data :=
  match raw with
  | .Constr tag (.Constr txTag fields :: rest) =>
    .Constr tag (.Constr txTag (fields.modify 9 fun
      | .Map entries => .Map (earlier ++ entries)
      | other => other) :: rest)
  | other => other

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
  earlierRedeemers : List (Data × Data)

/-- Split the redeemer map at the current entry, preserving both sides.
    Preserve malformed non-map fields, as spendingContext does. -/
def unpackSpendingContext : Data → Option SpendingFrame
  | .Constr 0 [.Constr 0 [.List inputs, referenceInputs, .List outputs, fee, mint,
      certificates, withdrawals, validRange, .List signers, redeemers, datums,
      txId, votes, proposals, treasury, donation], redeemer,
      .Constr 1 [reference, .Constr 0 [datum]]] => do
    let (earlierRedeemers, redeemers) ← match redeemers with
      | .Map entries => do
        let (earlier, currentAndLater) := entries.span (fun (purpose, _) => purpose != .Constr 1 [reference])
        let (_, value) :: later := currentAndLater | none
        if value == redeemer then some (earlier, .Map later) else none
      | raw => some ([], raw)
    return {
      inputs := inputs, outputs := outputs, signers := signers, validRange := validRange
      reference := reference, datum := datum, redeemer := redeemer, earlierRedeemers := earlierRedeemers
      unused := {
        referenceInputs := referenceInputs, fee := fee, mint := mint
        certificates := certificates, withdrawals := withdrawals, redeemers := redeemers
        datums := datums, txId := txId, votes := votes, proposals := proposals
        treasury := treasury, donation := donation } }
  | _ => none

/-- The initial common spending domain leaves these auxiliary fields empty.
    The current and earlier spending redeemers are carried separately. -/
def RawUnusedTxInfo.sharedDefaults : RawUnusedTxInfo := {}

private def v2Reference : Data → Option Data
  | .Constr 0 [.B txId, .I index] => some (.Constr 0 [.Constr 0 [.B txId], .I index])
  | _ => none

private def v2Input : Data → Option Data
  | .Constr 0 [reference, output] => do
    return txInput (← v2Reference reference) output
  | _ => none

private def v2Redeemer : Data × Data → Option (Data × Data)
  | (.Constr 1 [reference], value) => do
    return (.Constr 1 [← v2Reference reference], value)
  | _ => none

private def v2TxInfo (inputs outputs signers : List Data) (range : Data) (u : RawUnusedTxInfo)
    (redeemers : List (Data × Data)) : Option Data := do
  let .I fee := u.fee | none
  let .Map mint := u.mint | none
  let .B txId := u.txId | none
  let inputs ← inputs.mapM v2Input
  return .Constr 0 [
    .List inputs, u.referenceInputs, .List outputs, lovelace fee,
    .Map ((.B "", .Map [(.B "", .I 0)]) :: mint), u.certificates,
    u.withdrawals, range, .List signers, .Map redeemers, u.datums, .Constr 0 [.B txId]]

/-- Encode the same structured spend for V2. Outputs, signers, validity range,
    datum witnesses and payloads retain their common encodings. -/
def SpendingFrame.v2Arguments (frame : SpendingFrame) : Option (List Term) := do
  let u := frame.unused
  let d := RawUnusedTxInfo.sharedDefaults
  unless u.referenceInputs == d.referenceInputs && u.certificates == d.certificates &&
      u.withdrawals == d.withdrawals && u.redeemers == d.redeemers &&
      u.votes == d.votes && u.proposals == d.proposals &&
      u.treasury == d.treasury && u.donation == d.donation do none
  let .I fee := u.fee | none
  let .Map mint := u.mint | none
  let .B txId := u.txId | none
  let inputs ← frame.inputs.mapM v2Input
  let reference ← v2Reference frame.reference
  let earlier ← frame.earlierRedeemers.mapM v2Redeemer
  let purpose := Data.Constr 1 [reference]
  let tx := Data.Constr 0 [
    .List inputs, u.referenceInputs, .List frame.outputs, lovelace fee,
    .Map ((.B "", .Map [(.B "", .I 0)]) :: mint), u.certificates,
    u.withdrawals, frame.validRange, .List frame.signers,
    .Map (earlier ++ [(purpose, frame.redeemer)]), u.datums, .Constr 0 [.B txId]]
  return [.Const (.Data frame.datum), .Const (.Data frame.redeemer),
    .Const (.Data (.Constr 0 [tx, purpose]))]

def v2Arguments : List Term → Option (List Term)
  | [.Const (.Data raw)] => (unpackSpendingContext raw).bind SpendingFrame.v2Arguments
  | _ => none

/-- Both projections must be valid in their ledger models before checking acceptance. -/
def validSharedArguments (args : List Term) : Bool :=
  Ledger.validArguments args && match v2Arguments args with
    | some [.Const (.Data datum), .Const (.Data redeemer), .Const (.Data raw)] =>
      (CardanoLedgerApi.IsData.Class.IsData.fromData raw).any
        (fun ctx => CardanoLedgerApi.V2.Contexts.validSpendingContext ⟨datum, redeemer, ctx⟩)
    | _ => false

def spendingArguments (v3 : Bool) (args : List Term) : List Term :=
  if v3 then args else (v2Arguments args).getD []

private def v2MintingArguments : List Term → Option (List Term)
  | [.Const (.Data (.Constr 0 [.Constr 0 [.List inputs, .List [], .List outputs, fee, mint,
      .List [], .Map [], range, .List signers, .Map [(purpose, value)], datums, txId,
      .Map [], .List [], .Constr 1 [], .Constr 1 []], redeemer, .Constr 0 [.B symbol]]))] => do
    let key := Data.Constr 0 [.B symbol]
    unless purpose == key && value == redeemer do none
    let tx ← v2TxInfo inputs outputs signers range { fee, mint, datums, txId } [(key, redeemer)]
    return [.Const (.Data redeemer), .Const (.Data (.Constr 0 [tx, key]))]
  | _ => none

def validMintingArguments (useV2 useV3 : Bool) (args : List Term) : Bool :=
  (!useV3 || (match args with
    | [.Const (.Data raw)] => (Ledger.decode raw).any CardanoLedgerApi.V3.Contexts.validMintingContext
    | _ => false)) &&
  (!useV2 || (match v2MintingArguments args with
    | some [.Const (.Data redeemer), .Const (.Data raw)] =>
      (CardanoLedgerApi.IsData.Class.IsData.fromData raw).any
        (fun ctx => CardanoLedgerApi.V2.Contexts.validMintingContext ⟨redeemer, ctx⟩)
    | _ => false))

def mintingArguments (v3 : Bool) (args : List Term) : List Term :=
  if v3 then args else (v2MintingArguments args).getD []

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
