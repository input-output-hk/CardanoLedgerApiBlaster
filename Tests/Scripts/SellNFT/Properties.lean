import CardanoLedgerApi.V2
import Tests.Scripts.SellNFT.SellNFT
import Blaster

namespace Tests.Scripts.SellNFT
open CardanoLedgerApi.IsData.Class
open CardanoLedgerApi.Recursors
open CardanoLedgerApi.V2
open PlutusCore.Data (Data)
open PlutusCore.UPLC.Utils
open PlutusCore.Integer (Integer)

set_option warn.sorry false

structure SellDatum where
  seller : Address
  price : Integer

instance : IsData SellDatum where
  toData x := mkDataConstr 0 [IsData.toData x.seller, IsData.toData x.price]
  fromData
  | Data.Constr 0 [r_addr, Data.I p] =>
        match IsData.fromData r_addr with
        | some addr => some ⟨addr, p⟩
        | none => none
  | _ => none


def sellerIsPaid' (sellDatum : SellDatum) (amount : Integer) (ctx : ScriptContext) : Bool :=
  Recursor.any out in ctx.scriptContextTxInfo.txInfoOutputs =>
    out.txOutAddress = sellDatum.seller && lovelaceOf out.txOutValue ≥ amount

def sellerIsPaid (input : SpendingInput) : Prop :=
  match IsData.fromData input.datum with
  | some sell => sellerIsPaid' sell sell.price input.ctx
  | none => False


def getPrice (tinfo : TxInInfo) (ownInput : TxInInfo) (sellerAddress : Address) : Integer :=
 if tinfo.txInInfoOutRef != ownInput.txInInfoOutRef &&
    tinfo.txInInfoResolved.txOutAddress == ownInput.txInInfoResolved.txOutAddress
 then
   if let some dat := txOutInlineDatum tinfo.txInInfoResolved then
     if let some sell := (IsData.fromData dat : Option SellDatum)
     then if sell.seller == sellerAddress
          then sell.price
          else 0
     else 0
   else 0
 else 0

def no_multi_spent (input : SpendingInput) : Prop :=
  let rec accumulatedPrice (ownInput : TxInInfo) (sellerAddress : Address) (ins : List TxInInfo) : Integer :=
    match ins with
    | [] => 0
    | tinfo :: xs => getPrice tinfo ownInput sellerAddress + accumulatedPrice ownInput sellerAddress xs
  match findOwnInput input.ctx, IsData.fromData input.datum with
  | some ownInput, some sell =>
      let expectedAmount := sell.price + accumulatedPrice ownInput sell.seller input.ctx.scriptContextTxInfo.txInfoInputs
      sellerIsPaid' sell expectedAmount input.ctx
  | _, _ => false

/-- sellNFT successful → spending purpose ∧ seller is paid with expected Ada -/
theorem sell_nft_successful_imp_seller_is_paid :
  ∀ (input : SpendingInput),
     validSpendingContext input →
     isSuccessful (appliedSellNFT.prop input) →
     (isSpendingPurpose input.ctx ∧ sellerIsPaid input) := by blaster

/-- seller is not paid → sell nft errors -/
theorem seller_not_paid_sell_nft_error :
  ∀ (input : SpendingInput),
     validSpendingContext input →
     ¬ sellerIsPaid input →
     isUnsuccessful (appliedSellNFT.prop input) := by blaster

/-- not spending purpose → sell nft errors -/
theorem not_spending_purpose_imp_sell_nft_error :
  ∀ (input : SpendingInput),
     validSpendingContext input →
     ¬ isSpendingPurpose input.ctx →
     isUnsuccessful (appliedSellNFT.prop input) := by blaster

/-- Counterexample expected as sell nft is vulnerable against multi satisfaction -/
def success_imp_no_multi_spent : Prop :=
  ∀ (input: SpendingInput),
     validSpendingContext input →
     isSuccessful (appliedSellNFT.prop input) →
     no_multi_spent input

#blaster (gen-cex: 0) (solve-result: 1) (random-seed: 10) [success_imp_no_multi_spent]

/-- Counterexample expected if sell nft is succcessful when seller is not paid -/
def seller_not_paid_imp_success : Prop :=
  ∀ (input : SpendingInput),
     validSpendingContext input →
     ¬ sellerIsPaid input →
     isSuccessful (appliedSellNFT.prop input)

#blaster (gen-cex: 0) (solve-result: 1) [seller_not_paid_imp_success]

/-- Counterexample expected: There exists at least one valid SpendingInput for which SellNFT is successful -/
def cannot_unlock_nft : Prop :=
  ∀ (input : SpendingInput),
     validSpendingContext input →
    ¬ isSuccessful (appliedSellNFT.prop input)

#blaster (gen-cex: 0) (solve-result: 1) [cannot_unlock_nft]

end Tests.Scripts.SellNFT
