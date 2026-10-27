import Equivalence.Context

namespace Equivalence.Vesting

open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.UPLC.Term (Term)
open Context (Time)

abbrev UnusedTxInfo := Context.UnusedTxInfo

def beneficiary : ByteString := "beneficiary"
def policy : ByteString := "policy"
def token : ByteString := "vest"

def datum : Data := .Constr 0 [Context.pubKeyAddress beneficiary,
  .Constr 0 [.B policy, .B token], .I 1000, .I 0, .I 100, .I 10, .I 10]

def value (quantity : Int) (ada : Int := 2000000) : Data :=
  .Map ([(.B "", .Map [(.B "", .I ada)])] ++
    if quantity == 0 then [] else [(.B policy, .Map [(.B token, .I quantity)])])

def output (quantity : Int) : Data :=
  Context.txOutput Context.address (value quantity) (some datum)

def ownInput : Data := Context.txInput Context.ownRef
  (Context.setField (output 1000) 1 (value 1000 10000000))
def secondInput : Data := Context.txInput (Context.outputReference "ref-other")
  (Context.setField (output 1000) 1 (value 1000 10000000))

def context (unused : UnusedTxInfo) (inputs outputs signatories : List Data)
    (redeemer lower upper : Int) (hasTreasury hasDonation : Bool) : Data :=
  Context.spendingContext ((unused.raw outputs hasTreasury hasDonation).txInfo inputs signatories lower upper)
    (.Constr redeemer []) Context.ownRef datum

/-- Common symbolic parameters. Partial unlock fixes inputs and outputs rather
    than using those two lists; the erased binders simplify out of its queries. -/
abbrev Family := Context.Family

/-- Full unlock: lower bounds 99/100/101 around the fixed end 100, arbitrary
    upper bound, inputs, outputs, and unused fields. Authorization is absent, or
    the beneficiary is first with an arbitrary tail (the tail is not searched). -/
def fullArgs (time : Time) (signed hasTreasury hasDonation : Bool) : Family :=
  fun unused inputs outputs signatureTail upper =>
    Queries.contextArgs (context unused inputs outputs
      (Context.signatories signed beneficiary signatureTail)
      1 time.value upper hasTreasury hasDonation)

/-- Partial unlock at a chosen time/quantity; used for extra schedule probes. -/
def partialAtArgs (lower quantity : Int) (signed doubleInput hasTreasury hasDonation : Bool)
    (unused : UnusedTxInfo) (signatureTail : List Data) (upper : Int) : List Term :=
  Queries.contextArgs (context unused
    (if doubleInput then [ownInput, secondInput] else [ownInput]) [output quantity]
    (Context.signatories signed beneficiary signatureTail)
    0 lower upper hasTreasury hasDonation)

/-- Partial unlock: lower bounds 9/10/11 around the first-unlock threshold 10,
    remaining quantity 900 (correct at 11) or 901. Datum and asset are fixed;
    input count is one or two at the same address, with one continuing output. -/
def partialArgs (time : Time) (signed doubleInput correctQuantity hasTreasury hasDonation : Bool) : Family :=
  fun unused _ _ signatureTail upper => partialAtArgs (time.value - 90)
    (if correctQuantity then 900 else 901) signed doubleInput hasTreasury hasDonation unused signatureTail upper

/-- Finite control-flow choices, shared by symbolic queries and witness replay. -/
structure Case where
  time : Time
  signed : Bool
  doubleInput : Bool := false
  correctQuantity : Bool := true
  hasTreasury : Bool
  hasDonation : Bool

instance : Lean.ToExpr Case where
  toTypeExpr := Lean.mkConst ``Case
  toExpr c := Lean.mkAppN (Lean.mkConst ``Case.mk)
    #[Lean.toExpr c.time, Lean.toExpr c.signed, Lean.toExpr c.doubleInput, Lean.toExpr c.correctQuantity, Lean.toExpr c.hasTreasury, Lean.toExpr c.hasDonation]

def cases (isPartial : Bool) : Array Case := Id.run do
  let mut result := #[]
  for time in [Time.before, .at, .after] do
    for signed in [false, true] do
      for hasTreasury in [false, true] do
        for hasDonation in [false, true] do
          if isPartial then
            for doubleInput in [false, true] do
              for correctQuantity in [false, true] do
                result := result.push ⟨time, signed, doubleInput, correctQuantity, hasTreasury, hasDonation⟩
          else
            result := result.push { time, signed, hasTreasury, hasDonation }
  return result

def Case.args (c : Case) (isPartial : Bool) : Family :=
  if isPartial then partialArgs c.time c.signed c.doubleInput c.correctQuantity c.hasTreasury c.hasDonation
  else fullArgs c.time c.signed c.hasTreasury c.hasDonation

open Context (setField modifyField)

def otherOutput : Data := Context.txOutput (Context.scriptAddress "other-script") (value 1000)
def otherInput (i : Nat) : Data := Context.txInput (Context.outputReference "other" i) otherOutput

/-- Paired probes change only their inspected fields, preserving earlier mutations
    to unused fields or the spending datum. -/
private def partialProbe (lower quantity : Int) (s : Context.Sample) : Context.Sample :=
  let s := s.mapRedeemer (fun _ => .Constr 0 [])
  { s with signed := true, context :=
    modifyField s.context 0 fun tx =>
      setField (setField (setField (setField tx 0 (.List [s.ownInput]))
        2 (.List [output quantity]))
        8 (.List (.B beneficiary :: s.parameters.signatureTail))) 7 (Context.range lower s.parameters.timestamp) }

private def scanProbe (count : Nat) (s : Context.Sample) : Context.Sample :=
  let s := (partialProbe 50 500 s).scanInputs count otherOutput
  { s with context := modifyField s.context 0 fun tx =>
    setField tx 2 (.List (List.replicate count otherOutput ++ [output 500])) }

private def changeBeneficiary (s : Context.Sample) : Context.Sample :=
  let s := s.withoutSignatureTail
  s.mapDatum (fun d => setField d 0 (Context.pubKeyAddress "other-beneficiary"))

def variationGroups : List (List Context.Variation) := [
  Context.baselineGroup,
  Context.feeGroup,
  [.datum "datum-total" "spending datum total changed from 1000 to 1001" (fun d => setField d 2 (.I 1001)),
    .datum "datum-schedule" "spending datum first-unlock threshold changed from 10 to 20"
      (fun d => setField d 5 (.I 20)),
    Context.malformedDatum],
  [.datum "asset-policy" "spending datum asset policy changed"
    (fun d => setField d 1 (.Constr 0 [.B "other-policy", .B token])),
    .datum "asset-token" "spending datum asset token changed"
      (fun d => setField d 1 (.Constr 0 [.B policy, .B "other-token"]))],
  [⟨"beneficiary", "spending datum beneficiary changed; signature tail removed", changeBeneficiary⟩,
    .txInfo "output-address" "outputs replaced by one output of quantity 900 at a different address, with the original datum"
      (fun _ tx => setField tx 2 (.List [setField (output 900) 0 (Context.pubKeyAddress "other-address")]))],
  Context.constructorRedeemerGroup,
  Context.signerGroup,
  Context.inputGroup,
  [Context.emptyOutputs,
    .txInfo "outputs-two" "outputs replaced by two continuing outputs of quantity 900"
      (fun _ tx => setField tx 2 (.List [output 900, output 900])),
    .txInfo "quantity-zero" "outputs replaced by one continuing output of quantity 0"
      (fun _ tx => setField tx 2 (.List [output 0])),
    .txInfo "quantity-middle" "outputs replaced by one continuing output of quantity 500"
      (fun _ tx => setField tx 2 (.List [output 500])),
    .txInfo "quantity-total" "outputs replaced by one continuing output of quantity 1000"
      (fun _ tx => setField tx 2 (.List [output 1000]))],
  [.txInfo "time-49" "lower timestamp changed to 49"
    (fun s tx => setField tx 7 (Context.range 49 s.parameters.timestamp)),
    .txInfo "time-50" "lower timestamp changed to 50"
      (fun s tx => setField tx 7 (Context.range 50 s.parameters.timestamp)),
    .txInfo "time-51" "lower timestamp changed to 51"
      (fun s tx => setField tx 7 (Context.range 51 s.parameters.timestamp)),
    .txInfo "time-100" "lower timestamp changed to 100"
      (fun s tx => setField tx 7 (Context.range 100 s.parameters.timestamp))],
  [⟨"installment-first", "signed partial unlock at time 11 with 900 remaining, one own input", (partialProbe 11 900)⟩,
    ⟨"installment-middle", "signed partial unlock at time 50 with 500 remaining, one own input", (partialProbe 50 500)⟩,
    ⟨"installment-late", "signed partial unlock at time 91 with 100 remaining, one own input", (partialProbe 91 100)⟩,
    ⟨"installment-last", "signed partial unlock at time 99 with 100 remaining, one own input", (partialProbe 99 100)⟩],
  [⟨"lists-eight", "signed partial unlock at time 50 with 500 remaining; seven unrelated inputs, outputs and signers precede the required entries", (scanProbe 7)⟩,
    ⟨"lists-thirty-two", "signed partial unlock at time 50 with 500 remaining; thirty-one unrelated inputs, outputs and signers precede the required entries", (scanProbe 31)⟩]]

def catalog : List Context.Variation := variationGroups.flatten ++ Context.generalizationGroup

def variations : Array (String × String) := catalog.toArray.map Context.Variation.describe

def Case.fixture (c : Case) (isPartial : Bool) (p : Context.Parameters) : Context.Sample :=
  let inputs := if isPartial then (if c.doubleInput then [ownInput, secondInput] else [ownInput]) else p.inputs
  let outputs := if isPartial then [output (if c.correctQuantity then 900 else 901)] else p.outputs
  let ctx := context p.unused inputs outputs (Context.signatories c.signed beneficiary p.signatureTail)
    (if isPartial then 0 else 1) (if isPartial then c.time.value - 90 else c.time.value) p.timestamp c.hasTreasury c.hasDonation
  ⟨p, ctx, beneficiary, c.signed, ownInput, secondInput⟩

def Case.variedArgs (c : Case) (isPartial : Bool) (selection : String) : Family :=
  Context.explore (c.fixture isPartial) catalog (Context.variationNames selection)

def generalizedFamily (c : Case) (mode : String) (selection : List String) : Context.GeneralFamily :=
  fun general => Context.explore (c.fixture (mode == "vesting-partial")) catalog selection general

/-- Existing callers retain the fixture-only argument builder. -/
def family (c : Case) (mode : String) (selection : List String) : Context.Family :=
  generalizedFamily c mode selection {}

end Equivalence.Vesting
