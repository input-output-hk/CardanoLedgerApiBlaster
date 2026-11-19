/-
Linear vesting validator (FullUnlock only), fully symbolic `ScriptContext`.
Every two scripts of `scripts` are compared.
Run: lake lean equivalence/proofs/linear_vesting/LinearVestingList.lean
-/
import CardanoLedgerApi.V3
import Blaster

namespace Equivalence.Proofs.LinearVesting.LinearVestingList
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)
open PlutusCore.ByteString (ByteString)
open CardanoLedgerApi.IsData.Class
open CardanoLedgerApi.V3
open PlutusCore.UPLC.Utils
open PlutusCore.UPLC.CekMachine (State)

set_option warn.sorry false

-- Every script of `equivalence/examples/linear_vesting/`.
#import_uplc plinth145Script       PlutusV3 single_cbor_hex "equivalence/examples/linear_vesting/Plinth_1.45.0.0_Unisay.cbor_hex"
#import_uplc plinth145PlainScript  PlutusV3 single_cbor_hex "equivalence/examples/linear_vesting/Plinth_1.45.0.0_Unisay_plain.cbor_hex"
#import_uplc plinth161Script       PlutusV3 single_cbor_hex "equivalence/examples/linear_vesting/Plinth_1.61.0.0_Unisay.cbor_hex"
#import_uplc plinth164Script       PlutusV3 single_cbor_hex "equivalence/examples/linear_vesting/Plinth_1.64.0.0_Unisay.cbor_hex"
#import_uplc plinth164PlainScript  PlutusV3 single_cbor_hex "equivalence/examples/linear_vesting/Plinth_1.64.0.0_Unisay_plain.cbor_hex"
#import_uplc plinth165Script       PlutusV3 single_cbor_hex "equivalence/examples/linear_vesting/Plinth_1.65.0.0_Unisay.cbor_hex"
#import_uplc plinth165PlainScript  PlutusV3 single_cbor_hex "equivalence/examples/linear_vesting/Plinth_1.65.0.0_Unisay_plain.cbor_hex"
#import_uplc plinth167Script       PlutusV3 single_cbor_hex "equivalence/examples/linear_vesting/Plinth_1.67.0.0_Unisay.cbor_hex"
#import_uplc plinth167AsdataScript PlutusV3 single_cbor_hex "equivalence/examples/linear_vesting/Plinth_1.67.0.0_Unisay_asdata.cbor_hex"
#import_uplc scalus0182Script      PlutusV3 single_cbor_hex "equivalence/examples/linear_vesting/Scalus_0.18.2_Unisay.cbor_hex"

-- `#prep_uplc x xScript spendingInputs 1200` defines `x.prop : ScriptContext → State`: the
-- script `xScript` as a Lean function of the transaction. `x.prop ctx` is the final state of
-- the CEK machine (the UPLC evaluator) after running the script on `ctx`, with at most 1200
-- steps:
--   `.Halt _`: the script finished, i.e. it accepts the transaction (`isSuccessful`);
--   `.Error`: the script failed, i.e. it rejects the transaction, or it ran out of steps.
-- `spendingInputs ctx` is how the script is applied: a Plutus V3 spending script takes one
-- argument, the whole `ScriptContext` as `Data`; for a context that is not for spending it
-- gives an argument that makes the run fail. `#prep_uplc` runs the script on a symbolic
-- `ctx` and Blaster simplifies the result once here, so the theorems below don't redo it.
-- This is the slow step, so only the scripts used in `scripts` are prepared; see there why
-- the others are left out.
#prep_uplc plinth145       plinth145Script       spendingInputs 1200
-- #prep_uplc plinth145Plain  plinth145PlainScript  spendingInputs 1200
-- #prep_uplc plinth161       plinth161Script       spendingInputs 1200
#prep_uplc plinth164       plinth164Script       spendingInputs 1200
-- #prep_uplc plinth164Plain  plinth164PlainScript  spendingInputs 1200
-- #prep_uplc plinth165       plinth165Script       spendingInputs 1200
-- #prep_uplc plinth165Plain  plinth165PlainScript  spendingInputs 1200
-- #prep_uplc plinth167       plinth167Script       spendingInputs 1200
-- #prep_uplc plinth167Asdata plinth167AsdataScript spendingInputs 1200
-- #prep_uplc scalus0182      scalus0182Script      spendingInputs 1200

/-- The scripts to compare, each `x.prop` of a prepared script `x`: a function from the
transaction (`ScriptContext`) to the machine's final state (see the `#prep_uplc` lines). To
add one, uncomment its `#prep_uplc` line above too. `noncomputable`: `x.prop` is a term for
proofs, Lean doesn't compile it to run (`x.exec` is the runnable version). -/
noncomputable def scripts : List (ScriptContext → State) := [
  plinth145.prop,
  plinth164.prop,
  -- A valid FullUnlock needs more than the 1200-step budget (2606 and 2352 steps):
  -- plinth145Plain.prop,
  -- plinth165Plain.prop,
  -- Branch with `case` on a builtin result, which Blaster can't simplify:
  -- plinth161.prop,
  -- plinth164Plain.prop,
  -- plinth165.prop,
  -- plinth167.prop,
  -- plinth167Asdata.prop,
  -- scalus0182.prop,
]

/-- At most one signer: on these transactions every compared script finishes a FullUnlock
within the 1200-step budget (only signers add steps). -/
def SmallTx (ctx : ScriptContext) : Prop :=
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

/-! A valid FullUnlock (UPLC-CAPE fixture `successful_full_unlock`): the beneficiary signs,
after the vesting period (ends at 100), and takes all 1000 vested tokens. -/

/-- `n` copies of the byte `b`. -/
def bytes (b n : Nat) : ByteString := ⟨String.mk (List.replicate n (Char.ofNat b))⟩
/-- Who receives the vested tokens (UPLC-CAPE fixture). -/
def beneficiary : PubKeyHash := bytes 0xaa 32
/-- The address of a public key hash, without staking part. -/
def pkhAddress (pkh : PubKeyHash) : Address := ⟨.PubKeyCredential pkh, none⟩
/-- The vested token's currency symbol and name (UPLC-CAPE fixture). -/
def currencySymbol : ByteString := bytes 0xdd 28
def tokenName : ByteString := "vest"
/-- `VestingDatum beneficiary (AssetClass cs tn) total start end firstUnlock installments`. -/
def vestingDatum : Data :=
  Data.Constr 0 [IsData.toData (pkhAddress beneficiary),
    Data.Constr 0 [Data.B currencySymbol, Data.B tokenName],
    Data.I 1000, Data.I 0, Data.I 100, Data.I 10, Data.I 10]
/-- `FullUnlock` (constructor 1; PartialUnlock is constructor 0). Both have no fields. -/
def fullUnlockRedeemer : Data := Data.Constr 1 []
/-- The vesting UTxO the transaction spends: the script's "own" input. -/
def ownRef : TxOutRef := ⟨bytes 0x33 32, 0⟩
/-- A `Value` of `lovelace` lovelace and `vested` of the vested token. -/
def value (lovelace vested : Integer) : Value :=
  [(Data.B "", Data.Map [(Data.B "", Data.I lovelace)]),
   (Data.B currencySymbol, Data.Map [(Data.B tokenName, Data.I vested)])]

/-- Spends the vesting output (2 ada, 1000 tokens) to the beneficiary, valid from 101. -/
def fullUnlockCtx : ScriptContext :=
  ⟨{ txInfoInputs := [⟨ownRef, ⟨⟨.ScriptCredential (bytes 0x11 28), none⟩, value 2000000 1000,
                                .OutputDatum vestingDatum, none⟩⟩]
   , txInfoReferenceInputs := []
   , txInfoOutputs := [⟨pkhAddress beneficiary, value 1800000 1000, .NoOutputDatum, none⟩]
   , txInfoFee := 200000, txInfoMint := [], txInfoTxCerts := [], txInfoWdrl := []
   , txInfoValidRange := Data.Constr 0 [Data.Constr 0 [Data.Constr 1 [Data.I 101], Data.Constr 1 []],
                                        Data.Constr 0 [Data.Constr 2 [], Data.Constr 1 []]]
   , txInfoSignatories := [beneficiary]
   , txInfoRedeemers := [(.Spending ownRef, fullUnlockRedeemer)], txInfoData := []
   , txInfoId := bytes 0x99 32, txInfoVotes := []
   , txInfoProposalProcedures := []
   , txInfoCurrentTreasuryAmount := Data.Constr 1 [], txInfoTreasuryDonation := Data.Constr 1 [] },
   fullUnlockRedeemer, .SpendingScript ownRef (some vestingDatum)⟩

/-- 2. Not vacuous: every script accepts a valid FullUnlock, so (1) is not just "they reject
everything". -/
theorem all_accept : validSpendingContext fullUnlockCtx ∧ SmallTx fullUnlockCtx ∧
    AllAccept fullUnlockCtx scripts := by
  simp only [scripts, AllAccept, and_true]
  blaster (timeout: 120)

end Equivalence.Proofs.LinearVesting.LinearVestingList
