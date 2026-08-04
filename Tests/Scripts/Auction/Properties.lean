import Blaster
import CardanoLedgerApi.V3

import Tests.Scripts.Auction.Auction

namespace Tests.Scripts.Auction.Properties

open PlutusCore.Data (Data)
open PlutusCore.Integer
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.Utils
open CardanoLedgerApi.IsData.Class
open CardanoLedgerApi.V3
open CardanoLedgerApi.V3.Contexts
open CardanoLedgerApi.V3.Tx

open Tests.Scripts.Auction

set_option warn.sorry false

/-! # Common-vulnerability audit

Classification of the vulnerabilities in `.audits/README.md` for this *applied* auction validator.
`D` = defended (proved/demonstrated absent), `P` = present (demonstrated with an accepting witness),
`Δ` = design/economic (not a validator-level property), `-` = not applicable to this script.
The named properties/theorems appear further down this file.

| #  | Vulnerability                           | Verdict | Where / why |
|---:|-----------------------------------------|:-------:|-------------|
|  1 | Business logic                          | D       | `succeedsNewBid`/`succeedsPayout` economic properties |
|  2 | UTxO Value Size Spam (Token Dust)       | P       | `newBid_accepts_dust_tokens` |
|  3 | Large / Unbounded Protocol Datum        | -       | datum is `Maybe Bid` (bounded) |
|  4 | UTxO Concurrency DoS                    | Δ       | single continuing output serializes bids; exploitable as a cheap front-run DoS — outbid a pending bid by the minimal `+1` to invalidate it (`newBid_accepts_minimal_increment`). Tx-ordering, not a single-validator property. See #5, #23 |
|  5 | Cheap spam                              | Δ       | the minimal accepted increment is `+1` lovelace and the outbid bidder is refunded, so repeated griefing outbids are cheap (`newBid_accepts_minimal_increment`). See #4, #23 |
|  6 | Unauthorized Data modification          | D       | `nb_datum_wrong_bid_rejected` (new datum must equal the new bid) |
|  7 | Multisig PK Attack                      | -       | no multisig |
|  8 | Infinite Mint                           | P       | `newBid_ignores_minting` (validator never reads `txInfoMint`) |
|  9 | Other Token Name                        | D       | `nb_wrong_token_name_rejected` |
| 10 | Incorrect Parameterized Scripts         | D       | params baked in; properties reference `bakedMinBid`/`bakedEndTime` |
| 11 | Other Redeemer                          | D       | both redeemers covered; `nb_other_redeemer_rejected` |
| 12 | Foreign UTxO tokens                     | P       | `newBid_accepts_dust_tokens` (same root as #2) |
| 13 | Double or Multiple satisfaction         | P       | `payout_double_satisfaction` |
| 14 | Locked Ada                              | D       | `newBid_success_requires_output_locks_bid` (exact `==`, no excess ADA) |
| 15 | Locked non-Ada values                   | P       | dust tokens get locked in the continuing output (see #2) |
| 16 | Script output datum                     | D       | `nb_datum_hash_rejected`, `nb_datum_missing_rejected` (inline datum required) |
| 17 | Arbitrary UTxO datum                    | D       | `nb_datum_wrong_bid_rejected` (must decode to `Just newBid`) |
| 18 | Missing UTxO authentication             | P       | `valid_newBid_succeeds` holds with a spent input carrying NO NFT (safety delegated to the mint policy) |
| 19 | Lack of staking control                 | P       | payout outputs matched on payment key only: `payout_staked_outputs_accepted` (continuing output IS full-address matched) |
| 20 | Oracle Data attacks                     | -       | no oracle |
| 21 | Oracle PK attacks                       | -       | no oracle |
| 22 | Timestamp manipulation                  | D       | validity-range based (deterministic); `*_before_deadline` / `*_after_deadline` |
| 23 | Front-running                           | Δ       | open English auction on one UTxO: an attacker front-runs a pending bid with a minimal `+1` outbid, invalidating it (`newBid_accepts_minimal_increment`). See #4, #5 |
| 24 | Calculations                            | D       | covered by the bid-ordering / value properties |
| 25 | Sign checking of integer values         | D       | `newBid_success_positive_bid`, `payout_success_positive_asset` |
| 26 | Min Ada requirements                    | Δ       | validator doesn't enforce min-ada; `bakedMinBid = 100` lovelace < min-ada (ledger-level) |
-/

/-! ## The bounded `NewBid` scenario

The script is now the *applied* validator (`auctionValidatorScript`, see `QuickStart.hs`),
so it takes only the `ScriptContext`; the `AuctionParams` are baked in with the values below
(policy id = 28 zero bytes, token name = `"MY_TOKEN"`, min bid = 100, deadline = 1725227091000). -/

/-- Baked-in NFT minting policy id (`apCurrencySymbol` = 28 zero bytes). -/
def policyId : CurrencySymbol := ⟨String.mk (List.replicate 28 (Char.ofNat 0))⟩
/-- Baked-in NFT token name (`apTokenName = Value.tokenName "MY_TOKEN"`). -/
def nftName : TokenName := "MY_TOKEN"
/-- Baked-in minimum bid in lovelace (`apMinBid`). -/
abbrev bakedMinBid : Integer := 100
/-- Baked-in auction deadline in milliseconds (`apEndTime`). -/
abbrev bakedEndTime : Integer := 1725227091000

/-- The (symbolic-address, fixed) script being spent, reused for the consumed input and
    the continuing output so it is recognised as the continuing output. -/
def scriptAddr : Address  := ⟨.ScriptCredential "aa", none⟩
def ownRef     : TxOutRef := ⟨"bb", 0⟩

def oldBidAddr       := "oldAddr"
def oldBidPubKeyHash := "oldPKH"

/-- A `NewBid` transaction (no previous highest bid) with a fully concrete skeleton.
    Since the validator is applied, params are baked in; symbolic here are only `bidAmt`
    (the new bid), the continuing output's `outAda`/`outTok`, and the tx validity bound `hi`. -/
def newBidArgs (oldBidAmt newBidAmt outAda refundAda outTok hi : Integer) : List Term :=
  let bid           := ⟨"cc", "dd", newBidAmt⟩
  let consumedInput := ⟨scriptAddr, [], .NoOutputDatum, none⟩
  let datum : AuctionDatum :=
    if oldBidAmt ≤ 0
      then none
      else some ⟨oldBidAddr, oldBidPubKeyHash, oldBidAmt⟩
  let contValue :=
    [ (Data.B "", Data.Map [(Data.B "", Data.I outAda)])
    , (Data.B policyId, Data.Map [(Data.B nftName, Data.I outTok)])
    ]
  let contOutput :=
    ⟨scriptAddr, contValue, .OutputDatum (IsData.toData (some bid : AuctionDatum)), none⟩
  let refundOutput :=
    ⟨⟨.PubKeyCredential oldBidPubKeyHash, none⟩, [ (Data.B "", Data.Map [(Data.B "", Data.I refundAda)]) ], .NoOutputDatum, none⟩
  let outputs :=
    if refundAda > 0
      then [refundOutput, contOutput]
      else [contOutput]
  let validRange :=  -- the interval (-inf, hi]
    Data.Constr 0 [ Data.Constr 0 [Data.Constr 0 [], Data.Constr 1 []]
                  , Data.Constr 0 [Data.Constr 1 [Data.I hi], Data.Constr 1 []] ]
  let txInfo :=
    { txInfoInputs                := [⟨ownRef, consumedInput⟩]
    , txInfoReferenceInputs       := []
    , txInfoOutputs               := outputs
    , txInfoFee                   := 0
    , txInfoMint                  := []
    , txInfoTxCerts               := []
    , txInfoWdrl                  := []
    , txInfoValidRange            := validRange
    , txInfoSignatories           := []
    , txInfoRedeemers             := []
    , txInfoData                  := []
    , txInfoId                    := ""
    , txInfoVotes                 := []
    , txInfoProposalProcedures    := []
    , txInfoCurrentTreasuryAmount := Data.Constr 1 []
    , txInfoTreasuryDonation      := Data.Constr 1 []
    }
  let ctx : ScriptContext :=
    ⟨txInfo, IsData.toData (AuctionRedeemer.NewBid bid),
     ScriptInfo.SpendingScript ownRef (some (IsData.toData datum))⟩
  [toTerm ctx]

-- Optimizes to a genuine residual:
--   `Halt` iff `100 ≤ bidAmt ∧ hi ≤ 1725227091000 ∧ bidAmt = outAda ∧ outTok = 1`.
#prep_uplc appliedNewBid auction newBidArgs 60000

/-! ## Properties -/

/-- The bid succeeds (the script produces `BuiltinUnit`, i.e. halts). -/
abbrev succeedsNewBid (oldBidAmt newBidAmt outAda refundAda outTok hi : Integer) : Prop :=
  isSuccessful (appliedNewBid.prop oldBidAmt newBidAmt outAda refundAda outTok hi)

/-- Property, that states that the script cannot be satisfied by any arguments. -/
def newBidScriptAlwaysFails : Prop :=
  ∀ oldBidAmt newBidAmt outAda refundAda outTok hi,
  -------------------------------------------------
  ¬ succeedsNewBid oldBidAmt newBidAmt outAda refundAda outTok hi

/- Proves that newBidScriptAlwaysFails is False. -/
#blaster (solve-result: 1) (gen-cex: 0) [newBidScriptAlwaysFails]

/-- A successful bid must be at least the (baked-in) minimum bid (`sufficientBid`). -/
theorem newBid_success_requires_sufficient_bid (newBidAmt outAda outTok hi : Integer) :
    succeedsNewBid 0 newBidAmt outAda 0 outTok hi
    ---------------------------------------------
    → bakedMinBid ≤ newBidAmt := by blaster

/-- A successful bid must be bigger than the last valid bid. -/
theorem newBid_success_requires_bigger_bid (oldBidAmt newBidAmt outAda refundAda outTok hi : Integer) :
    succeedsNewBid oldBidAmt newBidAmt outAda refundAda outTok hi
    -------------------------------------------------------------
    → oldBidAmt < newBidAmt := by blaster

/-- A successful bid must be placed before the (baked-in) auction deadline (`validBidTime`):
    the transaction's validity upper bound `hi` cannot exceed `bakedEndTime`. -/
theorem newBid_success_requires_before_deadline (oldBidAmt newBidAmt outAda refundAda outTok hi : Integer) :
    succeedsNewBid oldBidAmt newBidAmt outAda refundAda outTok hi
    -------------------------------------------------------------
    → hi ≤ bakedEndTime := by blaster

/-- The continuing output must lock exactly the bid amount in lovelace
    (part of `correctOutput`). -/
theorem newBid_success_requires_output_locks_bid (oldBidAmt newBidAmt outAda refundAda outTok hi : Integer) :
    succeedsNewBid oldBidAmt newBidAmt outAda refundAda outTok hi
    -------------------------------------------------------------
    → outAda = newBidAmt := by blaster

/-- The continuing output must contain exactly one unit of the auctioned NFT
    (part of `correctOutput`). -/
theorem newBid_success_requires_single_nft (oldBidAmt newBidAmt outAda refundAda outTok hi : Integer) :
    succeedsNewBid oldBidAmt newBidAmt outAda refundAda outTok hi
    -------------------------------------------------------------
    → outTok = 1 := by blaster

/-- Conversely, whenever all five conditions hold the bid is accepted. -/
theorem valid_newBid_succeeds (oldBidAmt newBidAmt outAda refundAda outTok hi : Integer) :
    bakedMinBid ≤ newBidAmt →
    oldBidAmt < newBidAmt   →
    hi ≤ bakedEndTime       →
    outAda = newBidAmt      →
    refundAda = oldBidAmt   →
    outTok = 1
    ---------------------------
    → succeedsNewBid oldBidAmt newBidAmt outAda refundAda outTok hi := by blaster

/-- On-chain enabler of the concurrency / cheap-spam / front-running DoS (audit #4/#5/#23):
    a bid that outbids the current highest by the **minimal `+1` lovelace** is accepted. An
    attacker who sees a pending honest bid can therefore front-run it with a `+1` outbid (the
    outbid bidder is refunded, so it is cheap), spend the single auction UTxO first, and thereby
    invalidate the honest transaction. The DoS itself is a transaction-ordering phenomenon, not a
    single-validator property — this theorem only captures that the minimal increment suffices. -/
theorem newBid_accepts_minimal_increment (oldBidAmt outAda refundAda outTok hi : Integer) :
    bakedMinBid ≤ oldBidAmt + 1 →
    hi ≤ bakedEndTime          →
    outAda = oldBidAmt + 1     →
    refundAda = oldBidAmt      →
    outTok = 1
    -----------------------------------------------------------------------
    → succeedsNewBid oldBidAmt (oldBidAmt + 1) outAda refundAda outTok hi := by blaster



/-! ## The `Payout` scenario

`Payout` closes the auction once the deadline has passed: the seller receives the highest bid,
and the highest bidder receives the asset — or, if there were no bids, the asset returns to the
seller. The validator is applied, so `apSeller` (the seller's key hash) is baked in too. -/

/-- Baked-in seller public key hash (`apSeller` = 40 zero bytes). -/
def sellerPKH : PubKeyHash := ⟨String.mk (List.replicate 40 (Char.ofNat 0))⟩

/-- A `Payout` transaction with a fully concrete skeleton. `bidAmt ≤ 0` models "no previous
    bid" (the asset returns to the seller); `bidAmt > 0` models a highest bid that must be paid
    to the seller. Symbolic here are only the highest bid `bidAmt`, the lovelace `sellerAda`
    paid to the seller, the NFT quantity `assetTok` transferred to the winner, and the tx
    validity lower bound `lo`. -/
def payoutArgs (bidAmt sellerAda assetTok lo : Integer) : List Term :=
  let datum : AuctionDatum :=
    if 0 < bidAmt then some ⟨oldBidAddr, oldBidPubKeyHash, bidAmt⟩ else none
  let highestBidder : PubKeyHash := if 0 < bidAmt then oldBidPubKeyHash else sellerPKH
  let consumedInput := ⟨scriptAddr, [], .NoOutputDatum, none⟩
  let sellerOutput :=
    ⟨⟨.PubKeyCredential sellerPKH, none⟩, [ (Data.B "", Data.Map [(Data.B "", Data.I sellerAda)]) ], .NoOutputDatum, none⟩
  let assetOutput :=
    ⟨⟨.PubKeyCredential highestBidder, none⟩, [ (Data.B policyId, Data.Map [(Data.B nftName, Data.I assetTok)]) ], .NoOutputDatum, none⟩
  let outputs := if 0 < bidAmt then [sellerOutput, assetOutput] else [assetOutput]
  let validRange :=  -- the interval [lo, +inf)
    Data.Constr 0 [ Data.Constr 0 [Data.Constr 1 [Data.I lo], Data.Constr 1 []]
                  , Data.Constr 0 [Data.Constr 2 [], Data.Constr 1 []]
                  ]
  let txInfo :=
    { txInfoInputs                := [⟨ownRef, consumedInput⟩]
    , txInfoReferenceInputs       := []
    , txInfoOutputs               := outputs
    , txInfoFee                   := 0
    , txInfoMint                  := []
    , txInfoTxCerts               := []
    , txInfoWdrl                  := []
    , txInfoValidRange            := validRange
    , txInfoSignatories           := []
    , txInfoRedeemers             := []
    , txInfoData                  := []
    , txInfoId                    := ""
    , txInfoVotes                 := []
    , txInfoProposalProcedures    := []
    , txInfoCurrentTreasuryAmount := Data.Constr 1 []
    , txInfoTreasuryDonation      := Data.Constr 1 []
    }
  let ctx : ScriptContext :=
    ⟨txInfo, IsData.toData AuctionRedeemer.Payout,
     ScriptInfo.SpendingScript ownRef (some (IsData.toData datum))⟩
  [toTerm ctx]

-- Optimizes to a genuine residual:
--   `Halt` iff `bakedEndTime ≤ lo ∧ assetTok = 1 ∧ (0 < bidAmt → sellerAda = bidAmt)`.
#prep_uplc appliedPayout auction payoutArgs 60000

/-! ## Properties -/

/-- The payout succeeds (the script produces `BuiltinUnit`, i.e. halts). -/
abbrev succeedsPayout (bidAmt sellerAda assetTok lo : Integer) : Prop :=
  isSuccessful (appliedPayout.prop bidAmt sellerAda assetTok lo)

/-- Property, that states that the script cannot be satisfied by any arguments. -/
def payoutScriptAlwaysFails : Prop :=
  ∀ bidAmt sellerAda assetTok lo,
  -------------------------------
  ¬ succeedsPayout bidAmt sellerAda assetTok lo

/- Proves that payoutScriptAlwaysFails is False. -/
#blaster (solve-result: 1) (gen-cex: 0) [payoutScriptAlwaysFails]

/-- A successful payout may only happen once the (baked-in) deadline has passed
    (`validPayoutTime`): the transaction's validity lower bound `lo` is at least `bakedEndTime`. -/
theorem payout_success_requires_after_deadline (bidAmt sellerAda assetTok lo : Integer) :
    succeedsPayout bidAmt sellerAda assetTok lo
    -------------------------------------------
    → bakedEndTime ≤ lo := by blaster

/-- When there was a previous highest bid, a successful payout must pay the seller exactly that
    bid (`sellerGetsHighestBid`). -/
theorem payout_success_pays_seller_highest_bid (bidAmt sellerAda assetTok lo : Integer) :
    succeedsPayout bidAmt sellerAda assetTok lo →
    0 < bidAmt
    ----------------------------------------------
    → sellerAda = bidAmt := by blaster

/-- A successful payout must transfer exactly one unit of the auctioned NFT to the winner
    (`highestBidderGetsAsset`). -/
theorem payout_success_transfers_asset (bidAmt sellerAda assetTok lo : Integer) :
    succeedsPayout bidAmt sellerAda assetTok lo
    -------------------------------------------
    → assetTok = 1 := by blaster

/-- Conversely, with a previous highest bid, paying the seller that bid and the bidder the asset
    after the deadline is accepted. -/
theorem valid_payout_with_bid_succeeds (bidAmt sellerAda assetTok lo : Integer) :
    0 < bidAmt         →
    bakedEndTime ≤ lo  →
    sellerAda = bidAmt →
    assetTok = 1
    ---------------------
    → succeedsPayout bidAmt sellerAda assetTok lo := by blaster

/-- Conversely, with no previous bid, returning the asset to the seller after the deadline is
    accepted. -/
theorem valid_payout_no_bid_succeeds (sellerAda assetTok lo : Integer) :
    bakedEndTime ≤ lo →
    assetTok = 1
    --------------------
    → succeedsPayout 0 sellerAda assetTok lo := by blaster



open PlutusCore.UPLC.CekMachine (cekExecuteProgram)

def junkPolicy : CurrencySymbol := "junkcs"
def junkName   : TokenName      := "JUNK"
def ownRef2    : TxOutRef       := ⟨"bb", 1⟩

/-! ## Group 1 — Token dust / foreign tokens / unconstrained minting (PRESENT)

`newBidArgs` with an extra "junk" token (`junkTok`) added to the continuing output and an
arbitrary `txInfoMint` (`mintTok`). Neither is read by the validator, so both are accepted. -/

def newBidAttackArgs (oldBidAmt newBidAmt outAda refundAda outTok hi junkTok mintTok : Integer) : List Term :=
  let bid           := ⟨"cc", "dd", newBidAmt⟩
  let consumedInput := ⟨scriptAddr, [], .NoOutputDatum, none⟩
  let datum : AuctionDatum :=
    if oldBidAmt ≤ 0 then none else some ⟨oldBidAddr, oldBidPubKeyHash, oldBidAmt⟩
  let contValue :=
    [ (Data.B "", Data.Map [(Data.B "", Data.I outAda)])
    , (Data.B policyId, Data.Map [(Data.B nftName, Data.I outTok)])
    , (Data.B junkPolicy, Data.Map [(Data.B junkName, Data.I junkTok)])   -- extra dust asset
    ]
  let contOutput :=
    ⟨scriptAddr, contValue, .OutputDatum (IsData.toData (some bid : AuctionDatum)), none⟩
  let refundOutput :=
    ⟨⟨.PubKeyCredential oldBidPubKeyHash, none⟩, [ (Data.B "", Data.Map [(Data.B "", Data.I refundAda)]) ], .NoOutputDatum, none⟩
  let outputs := if refundAda > 0 then [refundOutput, contOutput] else [contOutput]
  let validRange :=
    Data.Constr 0 [ Data.Constr 0 [Data.Constr 0 [], Data.Constr 1 []]
                  , Data.Constr 0 [Data.Constr 1 [Data.I hi], Data.Constr 1 []] ]
  let txInfo :=
    { txInfoInputs                := [⟨ownRef, consumedInput⟩]
    , txInfoReferenceInputs       := []
    , txInfoOutputs               := outputs
    , txInfoFee                   := 0
    , txInfoMint                  := [ (Data.B junkPolicy, Data.Map [(Data.B junkName, Data.I mintTok)]) ]  -- unconstrained
    , txInfoTxCerts               := []
    , txInfoWdrl                  := []
    , txInfoValidRange            := validRange
    , txInfoSignatories           := []
    , txInfoRedeemers             := []
    , txInfoData                  := []
    , txInfoId                    := ""
    , txInfoVotes                 := []
    , txInfoProposalProcedures    := []
    , txInfoCurrentTreasuryAmount := Data.Constr 1 []
    , txInfoTreasuryDonation      := Data.Constr 1 []
    }
  let ctx : ScriptContext :=
    ⟨txInfo, IsData.toData (AuctionRedeemer.NewBid bid),
     ScriptInfo.SpendingScript ownRef (some (IsData.toData datum))⟩
  [toTerm ctx]

#prep_uplc appliedNewBidAttack auction newBidAttackArgs 60000

abbrev succeedsNewBidAttack (oldBidAmt newBidAmt outAda refundAda outTok hi junkTok mintTok : Integer) : Prop :=
  isSuccessful (appliedNewBidAttack.prop oldBidAmt newBidAmt outAda refundAda outTok hi junkTok mintTok)

/-- PRESENT — Token dust / Foreign UTxO tokens / UTxO value-size spam / Locked non-Ada:
    a valid bid is accepted even when the continuing output also carries an arbitrary extra token
    (`junkTok`) under a foreign policy. The validator never requires the output to hold ONLY the
    NFT + bid lovelace, so junk assets can be locked in alongside. -/
theorem newBid_accepts_dust_tokens
    (oldBidAmt newBidAmt outAda refundAda outTok hi junkTok : Integer) :
    bakedMinBid ≤ newBidAmt →
    oldBidAmt < newBidAmt   →
    hi ≤ bakedEndTime       →
    outAda = newBidAmt      →
    refundAda = oldBidAmt   →
    outTok = 1
    --------------------------
    → succeedsNewBidAttack oldBidAmt newBidAmt outAda refundAda outTok hi junkTok 0 := by blaster

/-- PRESENT — Infinite Mint / unconstrained minting: a valid bid is accepted regardless of what
    the transaction mints or burns (`mintTok` arbitrary); the spending validator never inspects
    `txInfoMint`. -/
theorem newBid_ignores_minting
    (oldBidAmt newBidAmt outAda refundAda outTok hi mintTok : Integer) :
    bakedMinBid ≤ newBidAmt →
    oldBidAmt < newBidAmt   →
    hi ≤ bakedEndTime       →
    outAda = newBidAmt      →
    refundAda = oldBidAmt   →
    outTok = 1
    --------------------------
    → succeedsNewBidAttack oldBidAmt newBidAmt outAda refundAda outTok hi 0 mintTok := by blaster

/-! ## Group 2 — Double / multiple satisfaction (PRESENT)

`payoutArgs` but the transaction spends TWO auction script inputs while providing only ONE seller
payment and ONE asset output. -/

def payoutDoubleSatArgs (bidAmt sellerAda assetTok lo : Integer) : List Term :=
  let datum : AuctionDatum :=
    if 0 < bidAmt then some ⟨oldBidAddr, oldBidPubKeyHash, bidAmt⟩ else none
  let highestBidder : PubKeyHash := if 0 < bidAmt then oldBidPubKeyHash else sellerPKH
  let consumedInput := ⟨scriptAddr, [], .NoOutputDatum, none⟩
  let sellerOutput :=
    ⟨⟨.PubKeyCredential sellerPKH, none⟩, [ (Data.B "", Data.Map [(Data.B "", Data.I sellerAda)]) ], .NoOutputDatum, none⟩
  let assetOutput :=
    ⟨⟨.PubKeyCredential highestBidder, none⟩, [ (Data.B policyId, Data.Map [(Data.B nftName, Data.I assetTok)]) ], .NoOutputDatum, none⟩
  let outputs := if 0 < bidAmt then [sellerOutput, assetOutput] else [assetOutput]
  let validRange :=
    Data.Constr 0 [ Data.Constr 0 [Data.Constr 1 [Data.I lo], Data.Constr 1 []]
                  , Data.Constr 0 [Data.Constr 2 [], Data.Constr 1 []] ]
  let txInfo :=
    { txInfoInputs                := [⟨ownRef, consumedInput⟩, ⟨ownRef2, consumedInput⟩]  -- TWO auction inputs
    , txInfoReferenceInputs       := []
    , txInfoOutputs               := outputs                                             -- ONE seller + ONE asset
    , txInfoFee                   := 0
    , txInfoMint                  := []
    , txInfoTxCerts               := []
    , txInfoWdrl                  := []
    , txInfoValidRange            := validRange
    , txInfoSignatories           := []
    , txInfoRedeemers             := []
    , txInfoData                  := []
    , txInfoId                    := ""
    , txInfoVotes                 := []
    , txInfoProposalProcedures    := []
    , txInfoCurrentTreasuryAmount := Data.Constr 1 []
    , txInfoTreasuryDonation      := Data.Constr 1 []
    }
  let ctx : ScriptContext :=
    ⟨txInfo, IsData.toData AuctionRedeemer.Payout,
     ScriptInfo.SpendingScript ownRef (some (IsData.toData datum))⟩
  [toTerm ctx]

#prep_uplc appliedPayoutDoubleSat auction payoutDoubleSatArgs 60000

abbrev succeedsPayoutDoubleSat (bidAmt sellerAda assetTok lo : Integer) : Prop :=
  isSuccessful (appliedPayoutDoubleSat.prop bidAmt sellerAda assetTok lo)

/-- PRESENT — Double / multiple satisfaction: the Payout validator accepts a transaction that
    spends TWO auction inputs while providing only ONE seller payment and ONE asset output. The
    seller/bidder checks use `List.find` (∃ one matching output) and never count inputs or require
    dedicated outputs, so a single payment can settle several auctions at once — the seller/bidder
    is underpaid.

    Modeling note: the validator is invoked once per spent script input against the *same*
    transaction; since it neither reads its own input nor counts outputs, both invocations reuse
    the same single seller/asset output — i.e. if this context is accepted for one input it is
    accepted for the other too. -/
theorem payout_double_satisfaction (bidAmt sellerAda assetTok lo : Integer) :
    0 < bidAmt         →
    bakedEndTime ≤ lo  →
    sellerAda = bidAmt →
    assetTok = 1
    ---------------------
    → succeedsPayoutDoubleSat bidAmt sellerAda assetTok lo := by blaster

/-! ## Group 3 — Sign checking & value defenses (over the existing props) -/

/-- DEFENDED — Sign checking: a successful bid is strictly positive (`apMinBid = 100 > 0`). -/
theorem newBid_success_positive_bid (oldBidAmt newBidAmt outAda refundAda outTok hi : Integer) :
    succeedsNewBid oldBidAmt newBidAmt outAda refundAda outTok hi
    -------------------------------------------------------------
    → 0 < newBidAmt := by blaster

/-- DEFENDED — Sign checking: a successful payout transfers a strictly positive NFT count. -/
theorem payout_success_positive_asset (bidAmt sellerAda assetTok lo : Integer) :
    succeedsPayout bidAmt sellerAda assetTok lo
    -------------------------------------------
    → 0 < assetTok := by blaster

/-- DEFENDED — Sign checking: when there is a highest bid, the seller payout is strictly positive. -/
theorem payout_success_positive_seller_payment (bidAmt sellerAda assetTok lo : Integer) :
    succeedsPayout bidAmt sellerAda assetTok lo →
    0 < bidAmt
    ----------------------------------------------
    → 0 < sellerAda := by blaster

/-! ## Group 4 — Structural defenses / weaknesses shown by concrete evaluation

blaster reasons over integers; these vary `Data`/`ByteString` structure, so they are checked by
evaluating the compiled UPLC on concrete contexts. `accepts c = true` ⇔ the script halts (accepts). -/

def demoCtx (inputs : List TxInInfo) (outputs : List TxOut) (red : Data) (vr : Data) (dat : AuctionDatum) : ScriptContext :=
  ⟨{ txInfoInputs                := inputs
   , txInfoReferenceInputs       := []
   , txInfoOutputs               := outputs
   , txInfoFee                   := 0
   , txInfoMint                  := []
   , txInfoTxCerts               := []
   , txInfoWdrl                  := []
   , txInfoValidRange            := vr
   , txInfoSignatories           := []
   , txInfoRedeemers             := []
   , txInfoData                  := []
   , txInfoId                    := ""
   , txInfoVotes                 := []
   , txInfoProposalProcedures    := []
   , txInfoCurrentTreasuryAmount := Data.Constr 1 [], txInfoTreasuryDonation := Data.Constr 1 []
   },
   red, ScriptInfo.SpendingScript ownRef (some (IsData.toData dat))
  ⟩

/-- The validator accepts (halts on) the concrete context `c`. -/
abbrev accepts (c : ScriptContext) : Prop :=
  isSuccessful (cekExecuteProgram auction.script [toTerm c] 50000)

def scriptInput  : TxInInfo := ⟨ownRef,  ⟨scriptAddr, [], .NoOutputDatum, none⟩⟩
def demoBid      : Bid := ⟨"cc", "dd", 200⟩
def demoRed      : Data := IsData.toData (AuctionRedeemer.NewBid demoBid)
def demoDatum    : OutputDatum := .OutputDatum (IsData.toData (some demoBid : AuctionDatum))
def demoRange    : Data := Data.Constr 0 [ Data.Constr 0 [Data.Constr 0 [], Data.Constr 1 []]
                                         , Data.Constr 0 [Data.Constr 1 [Data.I 1000], Data.Constr 1 []] ]
def adaE (n : Integer) : Data × Data := (Data.B "", Data.Map [(Data.B "", Data.I n)])
def tokE (pol : CurrencySymbol) (tn : TokenName) (n : Integer) : Data × Data := (Data.B pol, Data.Map [(Data.B tn, Data.I n)])
def contOut (val : Value) (od : OutputDatum) : TxOut := ⟨scriptAddr, val, od, none⟩

/-- A correct `NewBid` context (baseline for the demos below). -/
def demoValidCtx : ScriptContext :=
  demoCtx [scriptInput] [contOut [adaE 200, tokE policyId nftName 1] demoDatum] demoRed demoRange none
/-- Continuing output carries the NFT under a WRONG token name. -/
def demoWrongTnCtx : ScriptContext :=
  demoCtx [scriptInput] [contOut [adaE 200, tokE policyId junkName 1] demoDatum] demoRed demoRange none
/-- Continuing output carries an NFT under a WRONG minting policy. -/
def demoWrongPolicyCtx : ScriptContext :=
  demoCtx [scriptInput] [contOut [adaE 200, tokE junkPolicy nftName 1] demoDatum] demoRed demoRange none
/-- Continuing output uses a datum HASH instead of an inline datum. -/
def demoDatumHashCtx : ScriptContext :=
  demoCtx [scriptInput] [contOut [adaE 200, tokE policyId nftName 1] (.OutputDatumHash "h")] demoRed demoRange none
/-- Continuing output has no datum. -/
def demoNoDatumCtx : ScriptContext :=
  demoCtx [scriptInput] [contOut [adaE 200, tokE policyId nftName 1] .NoOutputDatum] demoRed demoRange none
/-- Continuing output's datum records a DIFFERENT bid than the redeemer's. -/
def demoWrongDatumCtx : ScriptContext :=
  demoCtx [scriptInput] [contOut [adaE 200, tokE policyId nftName 1] (.OutputDatum (IsData.toData (some ⟨"cc", "dd", 201⟩ : AuctionDatum)))] demoRed demoRange none
/-- An undefined redeemer constructor (`Constr 2`). -/
def demoOtherRedeemerCtx : ScriptContext :=
  demoCtx [scriptInput] [contOut [adaE 200, tokE policyId nftName 1] demoDatum] (Data.Constr 2 []) demoRange none
/-- A `Payout` whose seller/bidder outputs carry an (unconstrained) staking credential. -/
def demoPayoutStakedCtx : ScriptContext :=
  let stake : Option StakingCredential := some (.StakingHash (.PubKeyCredential "st"))
  demoCtx [scriptInput]
    [ ⟨⟨.PubKeyCredential sellerPKH, stake⟩, [adaE 200], .NoOutputDatum, none⟩
    , ⟨⟨.PubKeyCredential oldBidPubKeyHash, stake⟩, [tokE policyId nftName 1], .NoOutputDatum, none⟩ ]
    (IsData.toData AuctionRedeemer.Payout)
    (Data.Constr 0 [ Data.Constr 0 [Data.Constr 1 [Data.I bakedEndTime], Data.Constr 1 []]
                   , Data.Constr 0 [Data.Constr 2 [], Data.Constr 1 []] ])
    (some ⟨oldBidAddr, oldBidPubKeyHash, 200⟩)

theorem demo_valid_bid_accepted           : accepts demoValidCtx := by blaster
/-- DEFENDED — Other Token Name: the NFT must be the baked token name. -/
theorem nb_wrong_token_name_rejected      : ¬ accepts demoWrongTnCtx := by blaster
/-- DEFENDED — the NFT must be under the baked minting policy. -/
theorem nb_wrong_policy_rejected          : ¬ accepts demoWrongPolicyCtx := by blaster
/-- DEFENDED — Script output datum: an inline datum is required (a datum hash is rejected). -/
theorem nb_datum_hash_rejected            : ¬ accepts demoDatumHashCtx := by blaster
/-- DEFENDED — Script output datum: a missing datum is rejected. -/
theorem nb_datum_missing_rejected         : ¬ accepts demoNoDatumCtx := by blaster
/-- DEFENDED — Arbitrary UTxO datum / Unauthorized Data modification: the continuing datum must
    record exactly the new bid. -/
theorem nb_datum_wrong_bid_rejected       : ¬ accepts demoWrongDatumCtx := by blaster
/-- DEFENDED — Other Redeemer: an undefined redeemer constructor is rejected. -/
theorem nb_other_redeemer_rejected        : ¬ accepts demoOtherRedeemerCtx := by blaster
/-- PRESENT — Lack of staking control: payout outputs are matched on the payment key only, so an
    attacker-chosen staking credential on the seller/bidder outputs is still accepted. -/
theorem payout_staked_outputs_accepted    : accepts demoPayoutStakedCtx := by blaster

end Tests.Scripts.Auction.Properties
