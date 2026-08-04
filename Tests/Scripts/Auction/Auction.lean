import PlutusCore.UPLC
import CardanoLedgerApi.V3

namespace Tests.Scripts.Auction

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


/-- info: Successfully decoded single CBOR hex 'Tests/Scripts/Auction/auction.cbor_hex' -/
#guard_msgs in
#import_uplc auction PlutusV3 single_cbor_hex "Tests/Scripts/Auction/auction.cbor_hex"

end Tests.Scripts.Auction
