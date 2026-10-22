import Equivalence.Context

namespace Equivalence.Escrow

open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open Context (setField)

-- Fixture encoding follows UPLC-CAPE's two_party_escrow scenario and
-- plinth-cape-submissions@f042fed, lib/TwoPartyEscrow/Fixture.hs.
-- CAPE decodes the party keys from hex, but uses ASCII for the script hash.
def buyer : ByteString := ⟨String.mk (List.replicate 32 (Char.ofNat 170))⟩
def seller : ByteString := ⟨String.mk (List.replicate 32 (Char.ofNat 187))⟩
def address : Data := Context.scriptAddress "1111111111111111111111111111111111111111111111111111111111"
def price : Int := 75000000
def depositTime : Int := 1000000
def deadline : Int := depositTime + 1800000

def datum (state : Int := 0) (time : Int := depositTime) : Data :=
  .Constr 0 [.Constr state [], .I time]

def value (quantity : Int) : Data := .Map [(.B "", .Map [(.B "", .I quantity)])]
def output (addr : Data) (quantity : Int) (d : Data := datum) : Data :=
  Context.txOutput addr (value quantity) (some d)
def ownInput : Data := Context.txInput Context.ownRef (output address price)
def secondInput : Data := Context.txInput (Context.outputReference "other-ref") (output address price)

/-- Split inspected control flow before solving; unused fields and the unused
    interval endpoint retain the shared unbounded symbolic domain. -/
structure Case where
  time : Context.Time
  signed : Bool
  amountDelta : Int
  hasTreasury : Bool
  hasDonation : Bool

instance : Lean.ToExpr Case where
  toTypeExpr := Lean.mkConst ``Case
  toExpr c := Lean.mkAppN (Lean.mkConst ``Case.mk)
    #[Lean.toExpr c.time, Lean.toExpr c.signed, Lean.toExpr c.amountDelta, Lean.toExpr c.hasTreasury, Lean.toExpr c.hasDonation]

def cases : Array Case := Id.run do
  let mut result := #[]
  for time in [Context.Time.before, .at, .after] do
    for signed in [false, true] do
      for delta in [-1, 0, 1] do
        for hasTreasury in [false, true] do
          for hasDonation in [false, true] do
            result := result.push ⟨time, signed, delta, hasTreasury, hasDonation⟩
  return result

def Case.variationGroups (c : Case) (mode : String) : List (List Context.Variation) :=
  let recipient := Context.pubKeyAddress (if mode == "escrow-accept" then seller else buyer)
  let quantity := price + c.amountDelta
  let out := output (if mode == "escrow-deposit" then address else recipient) quantity
  [
  Context.baselineGroup,
  Context.feeGroup,
  [.datum "state-accepted" "spending datum state changed to Accepted" (fun _ => datum 1),
    .datum "state-refunded" "spending datum state changed to Refunded" (fun _ => datum 2),
    Context.malformedDatum,
    .datum "datum-time" "spending deposit time increased by one millisecond"
      (fun _ => datum 0 (depositTime + 1))],
  [.redeemer "redeemer-invalid" "redeemer replaced by integer 3" (fun _ => .I 3),
    .redeemer "redeemer-constructor" "redeemer replaced by constructor 0" (fun _ => .Constr 0 [])],
  Context.signerGroup,
  Context.inputGroup,
  [.txInfo "inputs-empty" "inputs removed" (fun _ tx => setField tx 0 (.List [])),
    .input "input-address" "own input moved to an unrelated script credential"
      (fun s => setField s.ownInput 1 (output (Context.scriptAddress "other-script") price)),
    .input "input-value" "own input lovelace increased by one"
      (fun s => setField s.ownInput 1 (output address (price + 1)))],
  [Context.emptyOutputs,
    .txInfo "output-recipient" "sole output moved to an unrelated public key"
      (fun _ tx => setField tx 2 (.List [setField out 0 (Context.pubKeyAddress "other")])),
    .txInfo "payment-split" "payment split between two outputs to the required recipient"
      (fun _ tx => setField tx 2 (.List [output recipient 25000000, output recipient (quantity - 25000000)])),
    .txInfo "continuing-output" "an additional escrow output of one lovelace added"
      (fun _ tx => setField tx 2 (.List [out, output address 1]))],
  [.txInfo "output-datum" "sole output datum changed to Accepted"
    (fun _ tx => setField tx 2 (.List [setField out 2 (.Constr 2 [datum 1])])),
    .txInfo "output-no-datum" "sole output inline datum removed"
      (fun _ tx => setField tx 2 (.List [setField out 2 (.Constr 0 [])])),
    .txInfo "output-token" "one foreign token added to the sole output"
      (fun _ tx => setField tx 2 (.List [setField out 1
      (.Map [(.B "", .Map [(.B "", .I quantity)]), (.B "policy", .Map [(.B "token", .I 1)])])])),
    .txInfo "output-stake" "staking credential added to the sole output address"
      (fun _ tx => setField tx 2 (.List [setField out 0
      (setField (if mode == "escrow-deposit" then address else recipient) 1
        (.Constr 0 [.Constr 0 [.Constr 0 [.B "stake"]]]))]))],
  Context.infiniteBoundsGroup]

def variationGroups : List (List Context.Variation) :=
  (cases[0]?.map (fun c => c.variationGroups "escrow-refund")).getD []

def variations : Array (String × String) := variationGroups.flatten.toArray.map Context.Variation.describe

/-- Raw integer actions: Deposit=0, Accept=1, Refund=2. Relevant lists are
    bounded templates; the unused endpoint and unused fields remain symbolic. -/
def Case.fixture (c : Case) (mode : String) (p : Context.Parameters) : Context.Sample :=
  let isDeposit := mode == "escrow-deposit"
  let isAccept := mode == "escrow-accept"
  let signer := if isAccept then seller else buyer
  let lower := if isDeposit then p.timestamp else deadline + c.time.value - 100
  let upper := if isDeposit then depositTime + 1 + c.time.value - 100 else p.timestamp
  let out := output (if isDeposit then address else Context.pubKeyAddress signer) (price + c.amountDelta)
  let tx := (p.unused.raw [out] c.hasTreasury c.hasDonation).txInfo [ownInput]
    (Context.signatories c.signed signer p.signatureTail) lower upper
  let redeemer := Data.I (if isDeposit then 0 else if isAccept then 1 else 2)
  ⟨p, Context.spendingContext tx redeemer Context.ownRef datum, signer, c.signed, ownInput, secondInput⟩

def Case.args (c : Case) (mode selection : String) : Context.Family :=
  Context.explore (c.fixture mode) (c.variationGroups mode).flatten (Context.variationNames selection)

def family (c : Case) (mode : String) (selection : List String) : Context.Family :=
  Context.explore (c.fixture mode) (c.variationGroups mode).flatten selection

end Equivalence.Escrow
