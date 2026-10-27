import Equivalence.Queries
import Equivalence.Ledger

namespace Equivalence.Context

open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.UPLC.Term (Term Program)

/-- Shared boundary probes around timestamp 100. -/
inductive Time where
  | before
  | at
  | after
 deriving Repr

def Time.value : Time → Int
  | .before => 99
  | .at => 100
  | .after => 101

instance : Lean.ToExpr Time where
  toTypeExpr := Lean.mkConst ``Time
  toExpr
    | .before => Lean.mkConst ``Time.before
    | .at => Lean.mkConst ``Time.at
    | .after => Lean.mkConst ``Time.after

def pubKeyAddress (key : ByteString) : Data :=
  .Constr 0 [.Constr 0 [.B key], .Constr 1 []]

def scriptAddress (hash : ByteString) : Data :=
  .Constr 0 [.Constr 1 [.B hash], .Constr 1 []]

def outputReference (txId : ByteString) (index : Int := 0) : Data :=
  .Constr 0 [.B txId, .I index]

def ownRef : Data := outputReference "ref"
def address : Data := scriptAddress "script"

/-- V3 output encoding; values and reference scripts retain arbitrary raw Data.
    A supplied datum is inline; absence uses the no-datum constructor. -/
def txOutput (address value : Data) (datum : Option Data := none)
    (referenceScript : Data := .Constr 1 []) : Data :=
  .Constr 0 [address, value, match datum with
    | some d => .Constr 2 [d]
    | none => .Constr 0 [], referenceScript]

def txInput (reference output : Data) : Data := .Constr 0 [reference, output]

/-- Compare encoded output references without a recursive Data-list comparison. -/
def sameReference : Data → Data → Bool
  | .Constr tag [.B tx, .I index], .Constr tag' [.B tx', .I index'] =>
    tag == tag' && tx == tx' && index == index'
  | _, _ => false

def replaceInputDatum (reference datum : Data) (input : Data) : Data :=
  match input with
  | .Constr tag [inputReference, .Constr outputTag [addr, value, inlineDatum, script]] =>
    if sameReference inputReference reference then
      match inlineDatum with
      | .Constr 2 [_] => .Constr tag [inputReference,
          .Constr outputTag [addr, value, .Constr 2 [datum], script]]
      | _ => input
    else input
  | _ => input

def replaceInputDatums (reference datum : Data) : List Data → List Data
  | [] => []
  | input :: rest => replaceInputDatum reference datum input :: replaceInputDatums reference datum rest

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

/-- Keep the required signer ahead of the symbolic tail, so authorization does
    not require an unbounded list search. -/
def signatories (signed : Bool) (signer : ByteString) (tail : List Data) : List Data :=
  if signed then .B signer :: tail else []

/-- V3 spending ScriptContext, with a present spending datum. -/
def spendingContext (txInfo redeemer reference datum : Data) : Data :=
  .Constr 0 [withSpendingRedeemer reference redeemer txInfo, redeemer,
    .Constr 1 [reference, .Constr 0 [datum]]]

/-- Transform a present datum while preserving the surrounding script-info encoding. -/
def mapSpendingDatum (change : Data → Data) (scriptInfo : Data) : Data :=
  match scriptInfo with
  | .Constr tag [reference, .Constr option [d]] =>
    .Constr tag [reference, .Constr option [change d]]
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

/-- V3 TxInfo field order shared by all scenario domains. -/
def RawUnusedTxInfo.txInfo (unused : RawUnusedTxInfo) (inputs signatories : List Data)
    (lower upper : Int) : Data :=
  .Constr 0 [.List inputs, unused.referenceInputs, unused.outputs, unused.fee,
      unused.mint, unused.certificates, unused.withdrawals, range lower upper,
      .List signatories, unused.redeemers, unused.datums, unused.txId,
      unused.votes, unused.proposals, unused.treasury, unused.donation]

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

/-- Shared outer encodings for CLI exploration. Nested Data contents remain
    unbounded; these shapes alone do not establish full ledger validity. -/
structure UnusedTxInfo where
  referenceInputs : List Data := []
  fee : Int := 0
  mint : List (Data × Data) := []
  certificates : List Data := []
  withdrawals : List (Data × Data) := []
  redeemers : List (Data × Data) := []
  datums : List (Data × Data) := []
  txId : ByteString := "tx"
  votes : List (Data × Data) := []
  proposals : List Data := []
  treasury : Int := 0
  donation : Int := 0
  rawUnused : RawUnusedTxInfo := {}

/-- Option constructors are split before symbolic execution; their amounts are
    arbitrary integers when present. Outputs are handled separately. -/
def UnusedTxInfo.raw (unused : UnusedTxInfo) (outputs : List Data)
    (hasTreasury hasDonation : Bool) : RawUnusedTxInfo := {
  referenceInputs := .List unused.referenceInputs
  outputs := .List outputs
  fee := .I unused.fee
  mint := .Map unused.mint
  certificates := .List unused.certificates
  withdrawals := .Map unused.withdrawals
  redeemers := .Map unused.redeemers
  datums := .Map unused.datums
  txId := .B unused.txId
  votes := .Map unused.votes
  proposals := .List unused.proposals
  treasury := if hasTreasury then .Constr 0 [.I unused.treasury] else .Constr 1 []
  donation := if hasDonation then .Constr 0 [.I unused.donation] else .Constr 1 [] }

abbrev Family := UnusedTxInfo → List Data → List Data → List Data → Int → List Term

def setField (value : Data) (index : Nat) (field : Data) : Data :=
  match value with
  | .Constr tag fields => .Constr tag (fields.set index field)
  | other => other

/-- Update a constructor field only when it is present. -/
def modifyField (value : Data) (index : Nat) (change : Data → Data) : Data :=
  match value with
  | .Constr tag fields => .Constr tag (fields.modify index change)
  | other => other

/-- Independent symbols for widening inspected fields. They never borrow an
    unused TxInfo field, so composing variations cannot accidentally couple them. -/
structure GeneralFields where
  lower : Int := 0
  upper : Int := 0
  datum : Data := .I 0
  redeemer : Data := .I 0
  interval : Data := .I 0
  reference : Data := .I 0

abbrev GeneralFamily := GeneralFields → Family

/-- Named symbolic inputs remain flat in the solver quantifiers and are bundled
    only while building and transforming a fixture. -/
structure Parameters where
  unused : UnusedTxInfo
  inputs : List Data
  outputs : List Data
  signatureTail : List Data
  timestamp : Int
  general : GeneralFields := {}

/-- A supplied context and the fixture information used by generic mutations. -/
structure Sample where
  parameters : Parameters
  context : Data
  signer : ByteString
  signed : Bool
  ownInput : Data
  secondInput : Data

/-- Changed keys must not trigger an unbounded search through a symbolic tail. -/
def Sample.withoutSignatureTail (s : Sample) : Sample :=
  let ctx := modifyField s.context 0 fun tx =>
    setField tx 8 (.List (signatories s.signed s.signer []))
  { s with parameters := { s.parameters with signatureTail := [] }, context := ctx }

/-- Change the spending datum and the matching input's inline datum together.
    Other inputs and continuing outputs are independent UTxOs and retain their
    own datums. Keep the input template synchronized for later input mutations. -/
def Sample.mapDatum (s : Sample) (change : Data → Data) : Sample :=
  match s.context with
  | .Constr _ [_, _, .Constr _ [reference, .Constr _ [datum]]] =>
    let datum := change datum
    let context := modifyField s.context 2 (mapSpendingDatum (fun _ => datum))
    let context := modifyField context 0 fun tx => modifyField tx 0 fun inputs =>
      match inputs with
      | .List inputs => .List (replaceInputDatums reference datum inputs)
      | other => other
    { s with context, ownInput := replaceInputDatum reference datum s.ownInput }
  | _ => s

def Sample.mapRedeemer (s : Sample) (change : Data → Data) : Sample :=
  match s.context with
  | .Constr tag [txInfo, redeemer, info@(.Constr _ [reference, _])] =>
    let redeemer := change redeemer
    let txInfo := modifyField txInfo 9 fun entries => match entries with
      | .Map (_ :: tail) => .Map ((.Constr 1 [reference], redeemer) :: tail)
      | other => other
    { s with context := .Constr tag [txInfo, redeemer, info] }
  | _ => s

/-- Bounded irrelevant inputs and signers exercise linear scans. -/
def Sample.scanInputs (s : Sample) (count : Nat) (unrelatedOutput : Data) : Sample :=
  let inputs := (List.range count).map fun (i : Nat) => txInput (outputReference "other" i) unrelatedOutput
  let ctx := modifyField s.context 0 fun tx =>
    setField (setField tx 0 (.List (inputs ++ [s.ownInput]))) 8
      (.List (List.replicate count (.B "other") ++ .B s.signer :: s.parameters.signatureTail))
  { s with signed := true, context := ctx }

/-- Replace unused fields without changing inspected inputs, signers or bounds. -/
def RawUnusedTxInfo.replaceUnused (raw : RawUnusedTxInfo) (tx : Data) : Data :=
  let fields := [(1, raw.referenceInputs), (2, raw.outputs), (3, raw.fee), (4, raw.mint),
    (5, raw.certificates), (6, raw.withdrawals), (9, raw.redeemers), (10, raw.datums),
    (11, raw.txId), (12, raw.votes), (13, raw.proposals), (14, raw.treasury), (15, raw.donation)]
  fields.foldl (fun tx (index, value) => setField tx index value) tx

/-- Metadata and behavior travel together for shared and contract-specific probes. -/
structure Variation where
  name : String
  description : String
  apply : Sample → Sample

namespace Variation

def describe (v : Variation) : String × String := (v.name, v.description)

def context (name description : String) (change : Sample → Data) : Variation :=
  ⟨name, description, fun s => { s with context := change s }⟩

def txInfo (name description : String) (change : Sample → Data → Data) : Variation :=
  context name description fun s => modifyField s.context 0 (change s)

def datum (name description : String) (change : Data → Data) : Variation :=
  ⟨name, description, fun s => s.mapDatum change⟩

def redeemer (name description : String) (change : Data → Data) : Variation :=
  ⟨name, description, fun s => s.mapRedeemer change⟩

/-- Replacing an inspected input updates both its template and the input list,
    so a later generic input-count mutation keeps the changed input. Preserve
    the previous datum: these variations change input address/value fields. -/
def input (name description : String) (change : Sample → Data) : Variation :=
  ⟨name, description, fun s =>
    let input := change s
    let input := match s.ownInput with
      | .Constr _ [_, .Constr _ [_, _, datum, _]] =>
        modifyField input 1 fun output => setField output 2 datum
      | _ => input
    let ctx := modifyField s.context 0 fun tx => setField tx 0 (.List [input])
    { s with ownInput := input, context := ctx }⟩

end Variation

def baselineGroup : List Variation := [⟨"baseline", "unchanged boundary template", id⟩]
def feeGroup : List Variation := [
  .txInfo "fee-zero" "fee set to integer zero" (fun _ tx => setField tx 3 (.I 0)),
  .txInfo "fee-positive" "fee set to integer one" (fun _ tx => setField tx 3 (.I 1))]
def signerGroup : List Variation := [
  ⟨"signer-second", "required signer placed after another signer, before the arbitrary tail", fun s =>
    { s with signed := true, context := modifyField s.context 0 fun tx =>
      setField tx 8 (.List (.B "a-other-signer" :: .B s.signer :: s.parameters.signatureTail)) }⟩,
  ⟨"signer-missing", "signatories replaced by one unrelated signer", fun s =>
    { s with signed := false, context := modifyField s.context 0 fun tx =>
      setField tx 8 (.List [.B "other-signer"]) }⟩]
def inputGroup : List Variation := [
  .txInfo "inputs-one" "inputs replaced by the consumed input"
    (fun s tx => setField tx 0 (.List [s.ownInput])),
  .txInfo "inputs-three" "inputs replaced by own input and two distinct same-address inputs"
    (fun s tx => setField tx 0 (.List [s.ownInput, s.secondInput,
      setField s.secondInput 0 (outputReference "third-ref")]))]

/-- Widen fields independently; composing these removes fixture restrictions
    without replacing the whole context by unconstrained Data. -/
def generalizationGroup : List Variation := [
  .txInfo "time-any" "independent arbitrary integer lower and upper timestamps"
    (fun s tx => setField tx 7 (range s.parameters.general.lower s.parameters.general.upper)),
  .txInfo "inputs-any" "input list replaced by arbitrary-length arbitrary Data"
    (fun s tx => setField tx 0 (.List s.parameters.inputs)),
  .txInfo "outputs-any" "output list replaced by arbitrary-length arbitrary Data"
    (fun s tx => setField tx 2 (.List s.parameters.outputs)),
  .txInfo "signers-any" "signer list replaced by arbitrary-length arbitrary Data, without a required prefix"
    (fun s tx => setField tx 8 (.List s.parameters.signatureTail)),
  ⟨"datum-any", "spending datum and own input's inline datum replaced by independent arbitrary Data",
    fun s => s.mapDatum (fun _ => s.parameters.general.datum)⟩,
  ⟨"redeemer-any", "redeemer and spending redeemer-map entry replaced by independent arbitrary Data",
    fun s => s.mapRedeemer (fun _ => s.parameters.general.redeemer)⟩,
  .txInfo "interval-any" "entire validity interval replaced by independent arbitrary Data"
    (fun s tx => setField tx 7 s.parameters.general.interval),
  .context "reference-any" "spending reference replaced by independent arbitrary Data"
    (fun s => modifyField s.context 2 (fun info => setField info 0 s.parameters.general.reference))]

def malformedDatum : Variation :=
  .datum "datum-malformed" "spending datum replaced by an integer" (fun _ => .I 0)
def constructorRedeemerGroup : List Variation := [
  .redeemer "redeemer-tag" "redeemer constructor changed to 2" (fun _ => .Constr 2 []),
  .redeemer "redeemer-fields" "redeemer fields replaced by one integer" (fun d => match d with
    | .Constr tag _ => .Constr tag [.I 42]
    | other => other)]
def emptyOutputs : Variation :=
  .txInfo "outputs-empty" "outputs replaced by an empty list" (fun _ tx => setField tx 2 (.List []))
def inclusiveUpper : Variation :=
  .txInfo "upper-inclusive" "upper interval bound changed from exclusive to inclusive"
    (fun _ tx => modifyField tx 7 fun interval =>
      modifyField interval 1 fun upper => setField upper 1 (.Constr 1 []))
def infiniteBoundsGroup : List Variation := [
  .txInfo "lower-infinite" "lower interval bound replaced by negative infinity"
    (fun _ tx => modifyField tx 7 fun interval =>
      setField interval 0 (.Constr 0 [.Constr 0 [], .Constr 1 []])),
  .txInfo "upper-infinite" "upper interval bound replaced by positive infinity"
    (fun _ tx => modifyField tx 7 fun interval =>
      setField interval 1 (.Constr 0 [.Constr 2 [], .Constr 0 []]))]

/-- Common catalog; each fixture exposes the variations applicable to its domain. -/
def sharedVariations : List Variation :=
  baselineGroup ++ feeGroup ++ signerGroup ++ inputGroup ++ generalizationGroup ++ [malformedDatum] ++
    constructorRedeemerGroup ++ [emptyOutputs, inclusiveUpper] ++ infiniteBoundsGroup

/-- Compositions run from left to right; a later write to the same field wins. -/
def variationNames (selection : String) : List String :=
  (selection.splitOn ",").map String.trim

def applyVariations (catalog : List Variation) (selection : List String) (sample : Sample) : Sample :=
  selection.foldl (fun s name =>
    match catalog.find? (fun v => v.name == name) with
    | some variation => variation.apply s
    | none => s) sample

/-- Solving, replay and emitted queries use the same fixture and composition. -/
def explore (fixture : Parameters → Sample) (catalog : List Variation) (selection : List String)
    (general : GeneralFields := {}) : Family :=
  fun unused inputs outputs signatureTail timestamp =>
    let sample := fixture ⟨unused, inputs, outputs, signatureTail, timestamp, general⟩
    Queries.contextArgs (applyVariations catalog selection sample).context

/-- Flat, named binders let the CLI reconstruct the exact model for replay. -/
def familyAll (args : Family) (p : List Term → Prop) : Prop :=
  ∀ (referenceInputs : List Data) (fee : Int) (mint : List (Data × Data))
    (certificates : List Data) (withdrawals redeemers datums : List (Data × Data))
    (txId : ByteString) (votes : List (Data × Data)) (proposals : List Data)
    (treasury donation : Int) (inputs outputs signatureTail : List Data) (timestamp : Int)
    (rawReferenceInputs rawOutputs rawFee rawMint rawCertificates rawWithdrawals
      rawRedeemers rawDatums rawTxId rawVotes rawProposals rawTreasury rawDonation : Data),
    0 ≤ fee → 0 ≤ treasury → 0 ≤ donation →
    p (args ⟨referenceInputs, fee, mint, certificates, withdrawals, redeemers, datums,
      txId, votes, proposals, treasury, donation,
      ⟨rawReferenceInputs, rawOutputs, rawFee, rawMint, rawCertificates, rawWithdrawals,
        rawRedeemers, rawDatums, rawTxId, rawVotes, rawProposals, rawTreasury, rawDonation⟩⟩
      inputs outputs signatureTail timestamp)

/-- Keep symbols flat and named in SMT models, constructing the record only
    after quantification. Unused symbols disappear from narrower queries. -/
def generalizedAll (args : GeneralFamily) (p : List Term → Prop) : Prop :=
  ∀ (lowerTimestamp upperTimestamp : Int)
    (arbitraryDatum arbitraryRedeemer arbitraryInterval arbitraryReference : Data),
    familyAll (args ⟨lowerTimestamp, upperTimestamp, arbitraryDatum, arbitraryRedeemer,
      arbitraryInterval, arbitraryReference⟩) p

def generalizedRejected (args : GeneralFamily) (old : Program)
    (cpu memory : Nat) (v3 : Bool) : Prop :=
  generalizedAll args fun parameters =>
    Acceptance.accepts v3 (Acceptance.execute old parameters cpu memory v3) = some false

def generalizedAcceptancePreserved (args : GeneralFamily) (old new : Program)
    (cpu memory : Nat) (v3 : Bool) : Prop :=
  generalizedAll args fun parameters => Queries.acceptancePreserved parameters old new cpu memory v3

def generalizedNoAcceptanceRegression (args : GeneralFamily) (old new : Program)
    (cpu memory : Nat) (v3 : Bool) : Prop :=
  generalizedAll args fun parameters => Queries.noAcceptanceRegression parameters old new cpu memory v3

/-- Contract-independent spending domain. Only the common outer encodings are
    fixed: lists/maps/bytes and a nonnegative fee, a 16-field TxInfo, and spending
    ScriptInfo. The interval, reference, datum option and redeemer are arbitrary
    independent Data, including missing or malformed options. -/
def spendingFamily (spendingReference spendingDatumOption spendingRedeemer validRange
    treasuryField donationField : Data) : Family :=
  fun unused inputs outputs signatureTail _ =>
    let tx := (unused.raw outputs false false).txInfo inputs signatureTail 0 0
    let tx := setField (setField (setField tx 7 validRange) 14 treasuryField) 15 donationField
    Queries.contextArgs (.Constr 0 [tx, spendingRedeemer,
      .Constr 1 [spendingReference, spendingDatumOption]])

def spendingAll (p : List Term → Prop) : Prop :=
  ∀ spendingReference spendingDatumOption spendingRedeemer validRange treasuryField donationField : Data,
    familyAll (spendingFamily spendingReference spendingDatumOption spendingRedeemer
      validRange treasuryField donationField) p

def spendingAcceptancePreserved (old new : Program) (cpu memory : Nat) (v3 : Bool) : Prop :=
  spendingAll fun args => Queries.acceptancePreserved args old new cpu memory v3

def spendingRejected (old : Program) (cpu memory : Nat) (v3 : Bool) : Prop :=
  spendingAll fun args => Queries.rejected args old cpu memory v3

def spendingNoAcceptanceRegression (old new : Program) (cpu memory : Nat) (v3 : Bool) : Prop :=
  spendingAll fun args => Queries.noAcceptanceRegression args old new cpu memory v3

def familyAcceptancePreserved (args : Family) (old new : Program)
    (cpu memory : Nat) (v3 : Bool) : Prop :=
  familyAll args fun parameters => Queries.acceptancePreserved parameters old new cpu memory v3

def familyNoAcceptanceRegression (args : Family) (old new : Program)
    (cpu memory : Nat) (v3 : Bool) : Prop :=
  familyAll args fun parameters => Queries.noAcceptanceRegression parameters old new cpu memory v3

end Equivalence.Context
