/-
HTLC validator, fully symbolic `ScriptContext`.
Every two scripts of `scripts` are compared.
Run: lake lean equivalence/proofs/htlc/HtlcList.lean
-/
import CardanoLedgerApi.V3
import Blaster

namespace Equivalence.Proofs.Htlc.HtlcList
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)
open PlutusCore.ByteString (ByteString)
open CardanoLedgerApi.IsData.Class
open CardanoLedgerApi.V3
open PlutusCore.UPLC.Utils
open PlutusCore.UPLC.CekMachine (State)

set_option warn.sorry false

-- Every script of `equivalence/examples/htlc/`.
#import_uplc plinth145Script       PlutusV3 single_cbor_hex "equivalence/examples/htlc/Plinth_1.45.0.0_Unisay.cbor_hex"
#import_uplc plinth145AsdataScript PlutusV3 single_cbor_hex "equivalence/examples/htlc/Plinth_1.45.0.0_Unisay_asdata.cbor_hex"
#import_uplc plinth161Script       PlutusV3 single_cbor_hex "equivalence/examples/htlc/Plinth_1.61.0.0_Unisay.cbor_hex"
#import_uplc plinth164Script       PlutusV3 single_cbor_hex "equivalence/examples/htlc/Plinth_1.64.0.0_Unisay.cbor_hex"
#import_uplc plinth164AsdataScript PlutusV3 single_cbor_hex "equivalence/examples/htlc/Plinth_1.64.0.0_Unisay_asdata.cbor_hex"
#import_uplc plinth165Script       PlutusV3 single_cbor_hex "equivalence/examples/htlc/Plinth_1.65.0.0_Unisay.cbor_hex"
#import_uplc plinth165AsdataScript PlutusV3 single_cbor_hex "equivalence/examples/htlc/Plinth_1.65.0.0_Unisay_asdata.cbor_hex"
#import_uplc plinth167Script       PlutusV3 single_cbor_hex "equivalence/examples/htlc/Plinth_1.67.0.0_Unisay.cbor_hex"
#import_uplc plinth167AsdataScript PlutusV3 single_cbor_hex "equivalence/examples/htlc/Plinth_1.67.0.0_Unisay_asdata.cbor_hex"
#import_uplc scalus0160Script      PlutusV3 single_cbor_hex "equivalence/examples/htlc/Scalus_0.16.0_Unisay.cbor_hex"
#import_uplc scalus0170Script      PlutusV3 single_cbor_hex "equivalence/examples/htlc/Scalus_0.17.0_Unisay.cbor_hex"
#import_uplc scalus0182Script      PlutusV3 single_cbor_hex "equivalence/examples/htlc/Scalus_0.18.2_Unisay.cbor_hex"

-- `#prep_uplc x xScript spendingInputs 1800` defines `x.prop : ScriptContext → State`: the
-- script `xScript` as a Lean function of the transaction. `x.prop ctx` is the final state of
-- the CEK machine (the UPLC evaluator) after running the script on `ctx`, with at most 1800
-- steps:
--   `.Halt _`: the script finished, i.e. it accepts the transaction (`isSuccessful`);
--   `.Error`: the script failed, i.e. it rejects the transaction, or it ran out of steps.
-- `spendingInputs ctx` is how the script is applied: a Plutus V3 spending script takes one
-- argument, the whole `ScriptContext` as `Data`; for a context that is not for spending it
-- gives an argument that makes the run fail. `#prep_uplc` runs the script on a symbolic
-- `ctx` and Blaster simplifies the result once here, so the theorems below don't redo it.
-- This is the slow step, so only the scripts used in `scripts` are prepared; see there why
-- the others are left out.
#prep_uplc plinth145       plinth145Script       spendingInputs 1800
#prep_uplc plinth164       plinth164Script       spendingInputs 1800
--#prep_uplc scalus0160      scalus0160Script      spendingInputs 1800
-- #prep_uplc plinth165Asdata plinth165AsdataScript spendingInputs 1800
-- #prep_uplc plinth145Asdata plinth145AsdataScript spendingInputs 1800
-- #prep_uplc plinth161       plinth161Script       spendingInputs 1800
-- #prep_uplc plinth164Asdata plinth164AsdataScript spendingInputs 1800
-- #prep_uplc plinth165       plinth165Script       spendingInputs 1800
-- #prep_uplc plinth167       plinth167Script       spendingInputs 1800
-- #prep_uplc plinth167Asdata plinth167AsdataScript spendingInputs 1800
-- #prep_uplc scalus0170      scalus0170Script      spendingInputs 1800
-- #prep_uplc scalus0182      scalus0182Script      spendingInputs 1800

/-- The scripts to compare, each `x.prop` of a prepared script `x`: a function from the
transaction (`ScriptContext`) to the machine's final state (see the `#prep_uplc` lines). To
add one, uncomment its `#prep_uplc` line above too. `noncomputable`: `x.prop` is a term for
proofs, Lean doesn't compile it to run (`x.exec` is the runnable version). -/
noncomputable def scripts : List (ScriptContext → State) := [
  plinth145.prop,
  plinth164.prop,
  -- Differs from the others: accepts a Refund whose redeemer is any constructor other
  -- than 0 (e.g. `Constr 9 []`), which every other script rejects. Found by `all_agree`.
  --scalus0160.prop,
  -- Preparing it doesn't finish in 60 s:
  -- plinth165Asdata.prop,
  -- A minimal valid Claim needs 2117 steps, more than the 1800-step budget:
  -- plinth145Asdata.prop,
  -- Branch with `case` on a builtin result, which Blaster can't simplify:
  -- plinth161.prop,
  -- plinth164Asdata.prop,
  -- plinth165.prop,
  -- plinth167.prop,
  -- plinth167Asdata.prop,
  -- scalus0170.prop,
  -- scalus0182.prop,  -- same bytes as scalus0170
]

/-- At most two inputs and one signer: on these transactions every compared script finishes
within the 1800-step budget (only inputs and signers add steps). -/
def SmallTx (ctx : ScriptContext) : Prop :=
  ctx.scriptContextTxInfo.txInfoInputs.length ≤ 2 ∧
  ctx.scriptContextTxInfo.txInfoSignatories.length ≤ 1

/-- `f` and `g` accept the same small contexts, among those the ledger can produce
(`validSpendingContext`: the spent input exists, the datum and redeemer match, the
transaction is balanced, ...): for every such `ctx`, `f` accepts it exactly when `g` does.
`isSuccessful s` holds when the final state `s` is `.Halt _`. -/
def Agree (f g : ScriptContext → State) : Prop :=
  ∀ (ctx : ScriptContext), validSpendingContext ctx → SmallTx ctx →
    (isSuccessful (f ctx) ↔ isSuccessful (g ctx))

/-- `f` agrees (`Agree`) with every script of the list. -/
def AgreesWithAll (f : ScriptContext → State) : List (ScriptContext → State) → Prop
  | [] => True
  | g :: rest => Agree f g ∧ AgreesWithAll f rest

/-- `Agree` holds between every two scripts of the list: `AllAgree [a, b, c]` is
`(Agree a b ∧ Agree a c) ∧ Agree b c`. -/
def AllAgree : List (ScriptContext → State) → Prop
  | [] => True
  | f :: rest => AgreesWithAll f rest ∧ AllAgree rest

/-- Every script of the list accepts `ctx`. -/
def AllAccept (ctx : ScriptContext) : List (ScriptContext → State) → Prop
  | [] => True
  | f :: rest => isSuccessful (f ctx) ∧ AllAccept ctx rest

/-- 1. Every two scripts accept the same contexts. -/
theorem all_agree : AllAgree scripts := by
  -- One goal per pair, so each pair gets its own verdict and counterexample.
  simp only [scripts, AllAgree, AgreesWithAll, and_true]
  repeat' apply And.intro
  -- Blaster leaves a pair open when it has no answer (neither proved nor a difference found).
  all_goals (blaster (timeout: 60); first | done | fail "Blaster gave no answer for this pair")

/-! A valid Claim, following the UPLC-CAPE spec (`scenarios/htlc/htlc.md`): the recipient
signs, reveals the preimage of the hash in the datum, before the timeout (100). Blaster finds
no such context by itself within 120 s, so it is given. -/

/-- Who locked the funds and can take them back after the timeout (Refund). -/
def payer : PubKeyHash := ⟨String.mk (List.replicate 28 'b')⟩
/-- Who can take the funds before the timeout by revealing the preimage (Claim). -/
def recipient : PubKeyHash := ⟨String.mk (List.replicate 28 'a')⟩
/-- The secret whose SHA-256 hash is in the datum. -/
def preimage : ByteString := "secret"
/-- The address of a public key hash, without staking part. -/
def pkhAddress (pkh : PubKeyHash) : Address := ⟨.PubKeyCredential pkh, none⟩
/-- `HTLCDatum payer recipient hash timeout`. -/
def htlcDatum : Data :=
  Data.Constr 0 [IsData.toData (pkhAddress payer), IsData.toData (pkhAddress recipient),
    Data.B (PlutusCore.Crypto.Hash.sha2_256 preimage), Data.I 100]
/-- `Claim preimage` (constructor 0; Refund is constructor 1, without fields). -/
def claimRedeemer : Data := Data.Constr 0 [Data.B preimage]
/-- The HTLC UTxO the transaction spends: the script's "own" input. -/
def ownRef : TxOutRef := ⟨⟨String.mk (List.replicate 32 '3')⟩, 0⟩
/-- A `Value` of `n` lovelace and nothing else (ada's currency symbol and token name are both
empty). -/
def lovelace (n : Integer) : Value := [(Data.B "", Data.Map [(Data.B "", Data.I n)])]

/-- Spends the HTLC output (2 ada) to the recipient, valid in [98, 100). -/
def claimCtx : ScriptContext :=
  ⟨{ txInfoInputs := [⟨ownRef, ⟨⟨.ScriptCredential ⟨String.mk (List.replicate 28 '1')⟩, none⟩,
                                lovelace 2000000, .OutputDatum htlcDatum, none⟩⟩]
   , txInfoReferenceInputs := []
   , txInfoOutputs := [⟨pkhAddress recipient, lovelace 1800000, .NoOutputDatum, none⟩]
   , txInfoFee := 200000, txInfoMint := [], txInfoTxCerts := [], txInfoWdrl := []
   , txInfoValidRange := Data.Constr 0 [Data.Constr 0 [Data.Constr 1 [Data.I 98], Data.Constr 1 []],
                                        Data.Constr 0 [Data.Constr 1 [Data.I 100], Data.Constr 0 []]]
   , txInfoSignatories := [recipient]
   , txInfoRedeemers := [(.Spending ownRef, claimRedeemer)], txInfoData := []
   , txInfoId := ⟨String.mk (List.replicate 32 '9')⟩, txInfoVotes := []
   , txInfoProposalProcedures := []
   , txInfoCurrentTreasuryAmount := Data.Constr 1 [], txInfoTreasuryDonation := Data.Constr 1 [] },
   claimRedeemer, .SpendingScript ownRef (some htlcDatum)⟩

/-- 2. Not vacuous: every script accepts a valid Claim, so (1) is not just "they reject
everything". -/
theorem all_accept : validSpendingContext claimCtx ∧ SmallTx claimCtx ∧ AllAccept claimCtx scripts := by
  simp only [scripts, AllAccept, and_true]
  blaster (timeout: 120)

end Equivalence.Proofs.Htlc.HtlcList
