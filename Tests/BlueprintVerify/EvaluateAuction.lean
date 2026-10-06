import PlutusCore.UPLC.BlueprintEncoding.Basic
import CardanoLedgerApi.Examples.Auction
#import_blueprints RawAuction "plutus.json"
open CardanoLedgerApi.Examples.Auction
open CardanoLedgerApi.IsData.Class
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CekMachine
open PlutusCore.Default.Internal

def runAuction (ctx : CardanoLedgerApi.V3.Contexts.ScriptContext) :=
  cekExecuteProgramWithSemanticVariant BuiltinSemanticsVariant.defaultFunSemanticsVariantE
    RawAuction.auction.script [Term.Const (.Data (toLedgerData ctx))] 20000

#eval show IO Unit from do
  for (name, ctx) in [("first bid", newBidContext 0 100 100 0 1 1725227091000),
                     ("replacement bid", newBidContext 100 101 101 100 1 1725227091000),
                     ("payout with bid", payoutContext 100 100 1 1725227091000),
                     ("payout without bid", payoutContext 0 0 1 1725227091000),
                     ("upstream demo bid", demoValidCtx),
                     ("payout to staked outputs", demoPayoutStakedCtx),
                     ("dust tokens", newBidAttackContext 100 101 101 100 1 1725227091000 1 0),
                     ("unchecked minting", newBidAttackContext 100 101 101 100 1 1725227091000 1 999),
                     ("two input payout", payoutDoubleSatContext 100 100 1 1725227091000)] do
    match runAuction ctx with
    | .Halt (.VCon .Unit) => IO.println s!"PASS {name} returns native unit"
    | _ => throw (IO.userError s!"expected accepted {name}")
  for (name, ctx) in [("low first bid", newBidContext 0 99 99 0 1 1725227091000),
                     ("equal replacement bid", newBidContext 100 100 100 100 1 1725227091000),
                     ("underpaid seller", payoutContext 100 99 1 1725227091000),
                     ("wrong token name", demoWrongTnCtx),
                     ("wrong policy", demoWrongPolicyCtx),
                     ("hashed datum", demoDatumHashCtx),
                     ("missing datum", demoNoDatumCtx),
                     ("wrong bid datum", demoWrongDatumCtx),
                     ("other redeemer", demoOtherRedeemerCtx)] do
    match runAuction ctx with
    | .Error => IO.println s!"PASS {name} is rejected"
    | _ => throw (IO.userError s!"expected rejected {name}")

def stepsUsed : State → Nat → Nat → Nat
  | .Halt _, _, count => count
  | .Error, _, count => count
  | _, 0, count => count
  | state, n+1, count => stepsUsed (step BuiltinSemanticsVariant.defaultFunSemanticsVariantE state) n (count+1)
#eval show IO Unit from do
  for ctx in [newBidContext 0 100 100 0 1 1725227091000,
              newBidContext 100 101 101 100 1 1725227091000,
              payoutContext 100 100 1 1725227091000,
              payoutContext 0 0 1 1725227091000] do
    let .Program _ body := RawAuction.auction.script
    IO.println s!"concrete execution steps: {stepsUsed (initialState (applyParams body [Term.Const (.Data (toLedgerData ctx))])) 20000 0}"
