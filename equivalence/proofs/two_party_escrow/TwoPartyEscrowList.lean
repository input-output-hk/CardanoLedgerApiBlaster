/-
Two-party escrow validator, fixed transaction shape (`escrowCtx`).
Every two scripts of `scripts` are compared.
Run: lake lean equivalence/proofs/two_party_escrow/TwoPartyEscrowList.lean
-/
import CardanoLedgerApi.V3
import Blaster

namespace Equivalence.Proofs.TwoPartyEscrow.TwoPartyEscrowList
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)
open PlutusCore.ByteString (ByteString)
open PlutusCore.UPLC.Term (Term)
open CardanoLedgerApi.IsData.Class
open CardanoLedgerApi.V3
open PlutusCore.UPLC.Utils
open PlutusCore.UPLC.CekMachine (State)

set_option warn.sorry false

/-- `n` copies of the byte `b`. -/
def bytes (b n : Nat) : ByteString := ⟨String.mk (List.replicate n (Char.ofNat b))⟩
/-- A `Value` of `n` lovelace and nothing else (ada's currency symbol and token name are both
empty). -/
def ada (n : Integer) : Value := [(Data.B "", Data.Map [(Data.B "", Data.I n)])]
/-- The escrow UTxO the transaction spends: the script's "own" input. -/
def ownRef : TxOutRef := ⟨bytes 0x44 32, 0⟩
/-- The wallet UTxO that pays the fee. -/
def walletRef : TxOutRef := ⟨bytes 0x55 32, 0⟩

/-- The transaction shape compared here, as a function of the values that stay symbolic.

Fixed: two inputs (the escrow UTxO `ownRef` being spent, then the wallet UTxO `walletRef`),
two outputs to public key addresses without staking part, one signer, ada only, no minting,
certificates, withdrawals, reference inputs or votes.

Symbolic (the theorems hold for every value of them):
- `scriptHash`: the hash of the script the escrow UTxO sits at;
- `wallet`: the public key hash owning the wallet UTxO;
- `to1`, `to2`: the public key hashes the two outputs pay;
- `signer`: the only signer;
- `inAda`, `walletAda`: the lovelace in the escrow and in the wallet UTxO;
- `out1`, `out2`: the lovelace in the two outputs; `fee`: the fee;
- `range`: the validity range, as `Data` (an `Interval POSIXTime`);
- `redeemer`: any `Data` (the spec's redeemers are `I 0` Deposit, `I 1` Accept, `I 2` Refund);
- `datum`: the escrow's inline datum, any `Data` (the spec's is `Constr 0 [state, depositTime]`).
-/
def escrowCtx (scriptHash wallet to1 to2 signer : ByteString) (inAda walletAda out1 out2 fee : Integer)
    (range redeemer datum : Data) : ScriptContext :=
  ⟨{ txInfoInputs := [⟨ownRef, ⟨⟨.ScriptCredential scriptHash, none⟩, ada inAda, .OutputDatum datum, none⟩⟩,
                      ⟨walletRef, ⟨⟨.PubKeyCredential wallet, none⟩, ada walletAda, .NoOutputDatum, none⟩⟩]
   , txInfoReferenceInputs := []
   , txInfoOutputs := [⟨⟨.PubKeyCredential to1, none⟩, ada out1, .NoOutputDatum, none⟩,
                       ⟨⟨.PubKeyCredential to2, none⟩, ada out2, .NoOutputDatum, none⟩]
   , txInfoFee := fee, txInfoMint := [], txInfoTxCerts := [], txInfoWdrl := []
   , txInfoValidRange := range, txInfoSignatories := [signer]
   , txInfoRedeemers := [(.Spending ownRef, redeemer)], txInfoData := []
   , txInfoId := bytes 0x99 32, txInfoVotes := [], txInfoProposalProcedures := []
   , txInfoCurrentTreasuryAmount := Data.Constr 1 [], txInfoTreasuryDonation := Data.Constr 1 [] },
   redeemer, .SpendingScript ownRef (some datum)⟩

/-- How a script is applied to the shape: a Plutus V3 spending script takes one argument, the
whole `ScriptContext` as `Data` (`toTerm` encodes it). `#prep_uplc` applies each script to
`escrowArgs ...` with all 13 values symbolic. -/
def escrowArgs (scriptHash wallet to1 to2 signer : ByteString) (inAda walletAda out1 out2 fee : Integer)
    (range redeemer datum : Data) : List Term :=
  [toTerm (escrowCtx scriptHash wallet to1 to2 signer inAda walletAda out1 out2 fee range redeemer datum)]

/-- A script, run on the escrow shape. This is the type of `x.prop` after
`#prep_uplc x xScript escrowArgs 20000`: give it the 13 values of `escrowCtx`, in the same
order, and it returns the final state of the CEK machine (the UPLC evaluator) after running
script `x` on `escrowCtx scriptHash wallet ... datum`, with at most 20000 steps:
- `.Halt _`: the script finished, i.e. it accepts the transaction;
- `.Error`: the script failed, i.e. it rejects the transaction, or it ran out of steps.

So `isSuccessful (x.prop scriptHash wallet ... datum)` (the state is `.Halt _`) reads
"script `x` accepts this transaction". -/
abbrev EscrowRun := ByteString → ByteString → ByteString → ByteString → ByteString →
  Integer → Integer → Integer → Integer → Integer → Data → Data → Data → State

-- Every script of `equivalence/examples/two_party_escrow/`.
#import_uplc plinth145Script       PlutusV3 single_cbor_hex "equivalence/examples/two_party_escrow/Plinth_1.45.0.0_Unisay.cbor_hex"
#import_uplc plinth145PlainScript  PlutusV3 single_cbor_hex "equivalence/examples/two_party_escrow/Plinth_1.45.0.0_Unisay_plain.cbor_hex"
#import_uplc plinth161Script       PlutusV3 single_cbor_hex "equivalence/examples/two_party_escrow/Plinth_1.61.0.0_Unisay.cbor_hex"
#import_uplc plinth164Script       PlutusV3 single_cbor_hex "equivalence/examples/two_party_escrow/Plinth_1.64.0.0_Unisay.cbor_hex"
#import_uplc plinth164PlainScript  PlutusV3 single_cbor_hex "equivalence/examples/two_party_escrow/Plinth_1.64.0.0_Unisay_plain.cbor_hex"
#import_uplc plinth165Script       PlutusV3 single_cbor_hex "equivalence/examples/two_party_escrow/Plinth_1.65.0.0_Unisay.cbor_hex"
#import_uplc plinth165AsdataScript PlutusV3 single_cbor_hex "equivalence/examples/two_party_escrow/Plinth_1.65.0.0_Unisay_asdata.cbor_hex"
#import_uplc plinth167Script       PlutusV3 single_cbor_hex "equivalence/examples/two_party_escrow/Plinth_1.67.0.0_Unisay.cbor_hex"
#import_uplc plinth167AsdataScript PlutusV3 single_cbor_hex "equivalence/examples/two_party_escrow/Plinth_1.67.0.0_Unisay_asdata.cbor_hex"
#import_uplc scalus0182Script      PlutusV3 single_cbor_hex "equivalence/examples/two_party_escrow/Scalus_0.18.2_Unisay.cbor_hex"

-- `#prep_uplc x xScript escrowArgs 20000` defines `x.prop : EscrowRun` (see `EscrowRun`):
-- script `xScript`, applied to `escrowArgs` with symbolic values and run for at most 20000
-- steps, simplified by Blaster once here so the theorems below don't redo it. This is the
-- slow step, so only the scripts used in `scripts` are prepared; see there why the others
-- are left out.
#prep_uplc plinth145       plinth145Script       escrowArgs 20000
#prep_uplc plinth145Plain  plinth145PlainScript  escrowArgs 20000
-- #prep_uplc plinth161       plinth161Script       escrowArgs 20000
#prep_uplc plinth164       plinth164Script       escrowArgs 20000
-- #prep_uplc plinth164Plain  plinth164PlainScript  escrowArgs 20000
-- #prep_uplc plinth165       plinth165Script       escrowArgs 20000
#prep_uplc plinth165Asdata plinth165AsdataScript escrowArgs 20000
-- #prep_uplc plinth167       plinth167Script       escrowArgs 20000
-- #prep_uplc plinth167Asdata plinth167AsdataScript escrowArgs 20000
-- #prep_uplc scalus0182      scalus0182Script      escrowArgs 20000

/-- The scripts to compare, each an `EscrowRun` (`x.prop` of a prepared script `x`). To add
one, uncomment its `#prep_uplc` line above too. `noncomputable`: `x.prop` is a term for
proofs, Lean doesn't compile it to run (`x.exec` is the runnable version). -/
noncomputable def scripts : List EscrowRun := [
  -- Plinth 1.45 and 1.64 don't check the datum's constructor tag (they only read its fields),
  -- Plinth 1.45 plain and 1.65 asdata do: on a Refund whose datum is `Constr 8 [...]` instead
  -- of `Constr 0 [...]`, the first two accept and the other two reject. Found by `all_agree`.
  plinth145.prop,
  plinth164.prop,
  --plinth145Plain.prop, -- 145Plain and 165Asdata are equivalent
  --plinth165Asdata.prop,
  -- Branch with `case` on a builtin result, which Blaster can't simplify:
  -- plinth161.prop,
  -- plinth164Plain.prop,
  -- plinth165.prop,
  -- plinth167.prop,
  -- plinth167Asdata.prop,
  -- scalus0182.prop,
]

/-- `f` and `g` accept the same transactions of the escrow shape: for all values of the 13
symbolic values for which the transaction is one the ledger can produce
(`validSpendingContext`: balanced, positive fee, sorted inputs, the datum and redeemer
match, ...), `f` accepts it exactly when `g` does. -/
def Agree (f g : EscrowRun) : Prop :=
  ∀ (scriptHash wallet to1 to2 signer : ByteString) (inAda walletAda out1 out2 fee : Integer)
    (range redeemer datum : Data),
    validSpendingContext
      (escrowCtx scriptHash wallet to1 to2 signer inAda walletAda out1 out2 fee range redeemer datum) →
    (isSuccessful (f scriptHash wallet to1 to2 signer inAda walletAda out1 out2 fee range redeemer datum) ↔
     isSuccessful (g scriptHash wallet to1 to2 signer inAda walletAda out1 out2 fee range redeemer datum))

/-- `f` agrees (`Agree`) with every script of the list. -/
def AgreesWithAll (f : EscrowRun) : List EscrowRun → Prop
  | [] => True
  | g :: rest => Agree f g ∧ AgreesWithAll f rest

/-- `Agree` holds between every two scripts of the list: `AllAgree [a, b, c]` is
`(Agree a b ∧ Agree a c) ∧ Agree b c`. -/
def AllAgree : List EscrowRun → Prop
  | [] => True
  | f :: rest => AgreesWithAll f rest ∧ AllAgree rest

/-- 1. Every two scripts accept the same transactions. -/
theorem all_agree : AllAgree scripts := by
  -- One goal per pair, so each pair gets its own verdict and counterexample.
  simp only [scripts, AllAgree, AgreesWithAll, and_true]
  repeat' apply And.intro
  -- Blaster leaves a pair open when it has no answer (neither proved nor a difference found).
  all_goals (blaster (timeout: 60); first | done | fail "Blaster gave no answer for this pair")

/-! A valid Accept (UPLC-CAPE fixture `successful_accept`): the seller signs and receives
exactly the price, 75 ada, from an escrow in the `Deposited` state; a wallet input pays the
fee and gets the change. -/

/-- The buyer's public key hash, baked into the scripts (UPLC-CAPE fixture). -/
def buyer : ByteString := bytes 0xaa 32
/-- The seller's public key hash, baked into the scripts (UPLC-CAPE fixture). -/
def seller : ByteString := bytes 0xbb 32
/-- Someone else: owns the wallet UTxO and gets the change. -/
def other : ByteString := bytes 0xcc 32
/-- The escrow script's hash, as the Plinth scripts have it baked in: 58 bytes `0x31` (the
ASCII digit `1`). -/
def escrowScriptHash : ByteString := bytes 0x31 58
/-- `EscrowDatum Deposited depositTime`: `Constr 0 [state, depositTime]`, with state
`Constr 0 []` (Deposited) and the deposit made at time 1000000. -/
def depositedDatum : Data := Data.Constr 0 [Data.Constr 0 [], Data.I 1000000]
/-- The validity range `[0, +∞)`: `Interval (LowerBound (Finite 0) closed) (UpperBound
PosInf closed)`, as `Data`. -/
def fromZero : Data :=
  Data.Constr 0 [Data.Constr 0 [Data.Constr 1 [Data.I 0], Data.Constr 1 []],
                 Data.Constr 0 [Data.Constr 2 [], Data.Constr 1 []]]
/-- Accept (the spec's redeemer is a plain integer: 0 Deposit, 1 Accept, 2 Refund). -/
def acceptRedeemer : Data := Data.I 1

/-- Every script of the list accepts the valid Accept: `escrowCtx` with the escrow (75 ada)
at `escrowScriptHash`, a wallet UTxO of `other` (5 ada), 75 ada to the seller and 4.8 ada
change to `other`, fee 0.2 ada, signed by the seller, valid from 0, redeemer Accept, datum
Deposited. -/
def AllAccept : List EscrowRun → Prop
  | [] => True
  | f :: rest =>
      isSuccessful (f escrowScriptHash other seller other seller 75000000 5000000 75000000 4800000 200000
        fromZero acceptRedeemer depositedDatum) ∧ AllAccept rest

/-- 2. Not vacuous: every script accepts a valid Accept, so (1) is not just "they reject
everything". -/
theorem all_accept :
    validSpendingContext (escrowCtx escrowScriptHash other seller other seller 75000000 5000000
      75000000 4800000 200000 fromZero acceptRedeemer depositedDatum) ∧ AllAccept scripts := by
  simp only [scripts, AllAccept, and_true]
  blaster (timeout: 120)

end Equivalence.Proofs.TwoPartyEscrow.TwoPartyEscrowList
