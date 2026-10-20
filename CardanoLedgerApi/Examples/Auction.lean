-- Adapted from input-output-hk/CardanoLedgerApiBlaster auction-script-proofs
-- commit 7bff1f69c5827a97128b177b65ce84159dd4ca48. Scenario constructors, not validity proofs.
import PlutusCore.UPLC
import CardanoLedgerApi.V3

namespace CardanoLedgerApi.Examples.Auction

open PlutusCore.ByteString
open PlutusCore.Integer
open PlutusCore.Data (Data)
open PlutusCore.UPLC.Term (Term)
open CardanoLedgerApi.IsData.Class
open CardanoLedgerApi.V3
open CardanoLedgerApi.V3.Contexts

structure AuctionParams where
  seller         : PubKeyHash
  currencySymbol : CurrencySymbol
  tokenName      : TokenName
  minBid         : Integer
  auctionEndTime : POSIXTime
  deriving Repr

structure Bid where
  address    : ByteString
  pubKeyHash : PubKeyHash
  amount     : Integer
  deriving Repr

abbrev AuctionDatum := Option Bid

inductive AuctionRedeemer
  | NewBid : Bid → AuctionRedeemer
  | Payout : AuctionRedeemer
  deriving Repr

structure AuctionArguments where
  scriptParams : AuctionParams
  ctx          : ScriptContext
  deriving Repr

instance : IsData AuctionParams where
  toData p :=
    mkDataConstr 0 [
      IsData.toData p.seller,
      IsData.toData p.currencySymbol,
      IsData.toData p.tokenName,
      IsData.toData p.minBid,
      IsData.toData p.auctionEndTime
    ]
  fromData
    | Data.Constr 0 [Data.B seller, Data.B cs, Data.B tn, Data.I minBid, Data.I endTime] => some ⟨seller, cs, tn, minBid, endTime⟩
    | _ => none

instance : IsData Bid where
  toData b := mkDataConstr 0 [IsData.toData b.address, IsData.toData b.pubKeyHash, IsData.toData b.amount]
  fromData
    | Data.Constr 0 [Data.B addr, Data.B pkh, Data.I amt] => some ⟨addr, pkh, amt⟩
    | _ => none

instance : IsData AuctionRedeemer where
  toData
    | .NewBid bid => mkDataConstr 0 [IsData.toData bid]
    | .Payout     => mkDataConstr 1
  fromData
    | Data.Constr 0 [r_bid] =>
        match IsData.fromData r_bid with
        | some bid => some (.NewBid bid)
        | none     => none
    | Data.Constr 1 [] => some .Payout
    | _ => none



open CardanoLedgerApi.V3.Tx
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
def newBidContext (oldBidAmt newBidAmt outAda refundAda outTok hi : Integer) : ScriptContext :=
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
  ctx


/-- Baked-in seller public key hash (`apSeller` = 40 zero bytes). -/
def sellerPKH : PubKeyHash := ⟨String.mk (List.replicate 40 (Char.ofNat 0))⟩

/-- A `Payout` transaction with a fully concrete skeleton. `bidAmt ≤ 0` models "no previous
    bid" (the asset returns to the seller); `bidAmt > 0` models a highest bid that must be paid
    to the seller. Symbolic here are only the highest bid `bidAmt`, the lovelace `sellerAda`
    paid to the seller, the NFT quantity `assetTok` transferred to the winner, and the tx
    validity lower bound `lo`. -/
def payoutContext (bidAmt sellerAda assetTok lo : Integer) : ScriptContext :=
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
  ctx



-- Remaining scenarios from upstream main 9938562fd452351655fe2f6b63e583c62422687c.
def junkPolicy : CurrencySymbol := "junkcs"
def junkName : TokenName := "JUNK"
def ownRef2 : TxOutRef := ⟨"bb", 1⟩

def newBidAttackContext (oldBidAmt newBidAmt outAda refundAda outTok hi junkTok mintTok : Integer) : ScriptContext :=
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
  ctx

def payoutDoubleSatContext (bidAmt sellerAda assetTok lo : Integer) : ScriptContext :=
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
  ctx

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


end CardanoLedgerApi.Examples.Auction
