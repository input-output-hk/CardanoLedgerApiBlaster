import Equivalence.Context

namespace Equivalence.HTLC

open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.UPLC.Term (Term)

-- Compatibility names for the shared fixture helpers.
abbrev Time := Context.Time
namespace Time
export Context.Time (before «at» after)
def value (time : Time) : Int := Context.Time.value time
end Time

def payer : ByteString := "payer"
def recipient : ByteString := "recipient"
def preimage : ByteString := "secret"
def secretHash : ByteString := PlutusCore.Crypto.Hash.sha2_256 preimage

abbrev ownRef := Context.ownRef
abbrev address := Context.address
abbrev pubKeyAddress := Context.pubKeyAddress

def datum : Data := .Constr 0 [pubKeyAddress payer, pubKeyAddress recipient, .B secretHash, .I 100]

def ownInput : Data := Context.txInput ownRef (Context.txOutput address (.Map []) (some datum))
def secondInput : Data := Context.txInput (Context.outputReference "other-ref")
  (Context.txOutput address (.Map []) (some datum))

abbrev range := Context.range

def context (unused : Context.RawUnusedTxInfo) (redeemer : Data)
    (inputs signatories : List Data) (lower upper : Int) : Data :=
  Context.spendingContext (unused.txInfo inputs signatories lower upper) redeemer ownRef datum

/-- Unrelated inputs force a search before finding the own input. -/
def otherInput (i : Nat) : Data := Context.txInput (Context.outputReference "other" i)
  (Context.txOutput (Context.scriptAddress "other-script") (.Map []))

/-- Finite boundary choices, shared by symbolic queries and witness replay. -/
structure Case where
  time : Time
  signed : Bool
  doubleInput : Bool
  hasTreasury : Bool := false
  hasDonation : Bool := false

instance : Lean.ToExpr Case where
  toTypeExpr := Lean.mkConst ``Case
  toExpr c := Lean.mkAppN (Lean.mkConst ``Case.mk)
    #[Lean.toExpr c.time, Lean.toExpr c.signed, Lean.toExpr c.doubleInput, Lean.toExpr c.hasTreasury, Lean.toExpr c.hasDonation]

def cases : Array Case := Id.run do
  let mut result := #[]
  -- Keep the original first twelve indices for existing replay commands.
  for hasTreasury in [false, true] do
    for hasDonation in [false, true] do
      for time in [Time.before, .at, .after] do
        for signed in [false, true] do
          for doubleInput in [false, true] do
            result := result.push ⟨time, signed, doubleInput, hasTreasury, hasDonation⟩
  return result

open Context (setField modifyField)

private def changeParty (index : Nat) (key : ByteString) (s : Context.Sample) : Context.Sample :=
  let s := s.withoutSignatureTail
  { s with context := modifyField s.context 2 (Context.mapSpendingDatum
      (fun d => setField d index (pubKeyAddress key))) }

private def claimWith (c : Case) (secret : ByteString) (s : Context.Sample) : Context.Sample :=
  let ctx := modifyField (setField s.context 1 (.Constr 0 [.B secret])) 0 fun tx =>
    setField (setField tx 8 (.List (Context.signatories s.signed recipient s.parameters.signatureTail)))
      7 (range s.parameters.timestamp (c.time.value + 1))
  { s with signer := recipient, context := ctx }


def Case.variationGroups (c : Case) : List (List Context.Variation) := [
  Context.baselineGroup,
  Context.feeGroup,
  [.datum "datum-timeout-zero" "spending datum timeout changed to 0" (fun d => setField d 3 (.I 0)),
    .datum "datum-timeout-101" "spending datum timeout changed to 101" (fun d => setField d 3 (.I 101)),
    Context.malformedDatum],
  [⟨"payer", "spending datum payer changed; signature tail removed", (changeParty 0 "other-payer")⟩,
    ⟨"recipient", "spending datum recipient changed; signature tail removed", (changeParty 1 "other-recipient")⟩],
  [.datum "hash-empty" "spending datum secret hash replaced by empty bytes" (fun d => setField d 2 (.B "")),
    ⟨"secret-wrong", "claim template with an incorrect preimage, recipient authorization and claim interval bounds", (claimWith c "wrong")⟩,
    ⟨"secret-empty", "claim template with an empty preimage, recipient authorization and claim interval bounds", (claimWith c "")⟩],
  Context.constructorRedeemerGroup,
  Context.signerGroup,
  Context.inputGroup,
  [.input "input-address" "inputs replaced by own input at a different address"
    (fun s => setField s.ownInput 1 (Context.txOutput (pubKeyAddress "other-address") (.Map []) (some datum)))],
  [.txInfo "lower-zero" "lower timestamp changed to 0"
    (fun _ tx => modifyField tx 7 fun r => setField r 0 (.Constr 0 [.Constr 1 [.I 0], .Constr 1 []])),
    .txInfo "lower-101" "lower timestamp changed to 101"
      (fun _ tx => modifyField tx 7 fun r => setField r 0 (.Constr 0 [.Constr 1 [.I 101], .Constr 1 []])),
    .txInfo "upper-100" "exclusive upper timestamp changed to 100"
      (fun _ tx => modifyField tx 7 fun r => setField r 1 (.Constr 0 [.Constr 1 [.I 100], .Constr 0 []])),
    Context.inclusiveUpper],
  [.txInfo "raw-unused" "all thirteen unused TxInfo fields replaced by independent arbitrary raw Data, overriding outer encodings and amount restrictions"
    (fun s tx => s.parameters.unused.rawUnused.replaceUnused tx)],
  [⟨"inputs-eight", "seven unrelated inputs and signers precede the own input and required signer, followed by the arbitrary signature tail", (fun s => s.scanInputs 7 (Context.txOutput (Context.scriptAddress "other-script") (.Map [])))⟩],
  [⟨"unsigned-inputs", "signatures removed and input list replaced by arbitrary-length arbitrary Data", (fun s =>
      let ctx := modifyField s.context 0 fun tx =>
        setField (setField tx 0 (.List s.parameters.inputs)) 8 (.List [])
      { s with signed := false, context := ctx })⟩,
    .input "input-fields" "one own input with independently arbitrary raw value and reference-script Data"
      (fun s => setField s.ownInput 1 (Context.txOutput address s.parameters.unused.rawUnused.mint
      (some datum) s.parameters.unused.rawUnused.txId))]]

def variationGroups : List (List Context.Variation) :=
  (cases[0]?.map Case.variationGroups).getD []

private def signersBoth : Context.Variation :=
  .txInfo "signers-both" "signatories replaced by payer and recipient"
    (fun _ tx => setField tx 8 (.List [.B payer, .B recipient]))

def Case.catalog (c : Case) : List Context.Variation := c.variationGroups.flatten ++ [signersBoth]

def variations : Array (String × String) :=
  (variationGroups.flatten ++ [signersBoth]).toArray.map Context.Variation.describe

/-- One supplied fixture is used by every shared or contract-specific mutation. -/
def Case.fixture (c : Case) (isClaim : Bool) (p : Context.Parameters) : Context.Sample :=
  let signer := if isClaim then recipient else payer
  let lower := if isClaim then p.timestamp else c.time.value
  let upper := if isClaim then c.time.value + 1 else p.timestamp
  let tx := (p.unused.raw p.outputs c.hasTreasury c.hasDonation).txInfo
    (if c.doubleInput then [ownInput, secondInput] else [ownInput])
    (Context.signatories c.signed signer p.signatureTail) lower upper
  let redeemer := if isClaim then Data.Constr 0 [.B preimage] else .Constr 1 []
  ⟨p, Context.spendingContext tx redeemer ownRef datum, signer, c.signed, ownInput, secondInput⟩

def Case.exploreArgs (c : Case) (isClaim : Bool) (selection : String) : Context.Family :=
  Context.explore (c.fixture isClaim) c.catalog (Context.variationNames selection)

/-- Uniform entry point for native replay and symbolic CLI queries. -/
def family (c : Case) (mode : String) (selection : List String) : Context.Family :=
  Context.explore (c.fixture (mode == "htlc-claim")) c.catalog selection

end Equivalence.HTLC
