import WscDx.Script

/-! Minimal transaction vocabulary and the corrected, unshaped P1 statement
from the earlier CardanoLedgerApiBlaster work. No shaped context constructors,
proof summaries, or source-model acceptance predicate are imported. -/

namespace WscDx

open CardanoLedgerApi.V3
open CardanoLedgerApi.IsData.Class (IsData)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)

def payCred (o : TxOut) : Credential :=
  o.txOutAddress.addressCredential

def mintOf (cs : CurrencySymbol) (tn : TokenName) (mint : MintValue) : Integer :=
  valueOf cs tn mint

namespace Model

def outSum (base : Credential) (cs : CurrencySymbol) (tn : TokenName) : List TxOut → Integer
  | [] => 0
  | o :: rest =>
      (if WscDx.payCred o == base then valueOf cs tn o.txOutValue else 0)
      + outSum base cs tn rest

def inSum (base : Credential) (cs : CurrencySymbol) (tn : TokenName) : List TxInInfo → Integer
  | [] => 0
  | i :: rest =>
      (if WscDx.payCred i.txInInfoResolved == base then
         valueOf cs tn i.txInInfoResolved.txOutValue else 0)
      + inSum base cs tn rest

def headOpt {α : Type} : List α → Option α
  | [] => none
  | x :: _ => some x

def dropIdx {α : Type} (idx : Integer) (l : List α) : List α := l.drop idx.toNat

def atIdx {α : Type} (idx : Integer) (l : List α) : Option α :=
  headOpt (dropIdx idx l)

def hasCSH (cs : CurrencySymbol) : Value → Option Bool
  | [] => none                              -- ptail # pnil
  | _ :: rest =>
      match rest with
      | [] => none                          -- phead # pnil
      | (Data.B cs', _) :: _ => some (cs' == cs)
      | _ => none                           -- pfromData on a non-B key

def dirNodeInterval : Data → Option (CurrencySymbol × CurrencySymbol)
  | Data.List (Data.B k :: Data.B n :: _) => some (k, n)
  | _ => none

def exemptible (dirCS cs : CurrencySymbol) : List TxInInfo → Bool
  | [] => false
  | i :: rest =>
      (match i.txInInfoResolved.txOutDatum with
       | .OutputDatum d =>
           (match dirNodeInterval d with
            | some (k, n) =>
                decide (k < cs) && decide (cs < n) &&
                  (hasCSH dirCS i.txInInfoResolved.txOutValue == some true)
            | none => false)
       | _ => false)
      || exemptible dirCS cs rest

def exempt (dirCS cs : CurrencySymbol) (refs : List TxInInfo) : Bool :=
  (cs == ByteString.mk "") || exemptible dirCS cs refs

def isProgrammable (dirCS cs : CurrencySymbol) (refs : List TxInInfo) : Bool :=
  !(exempt dirCS cs refs)

def paramsDirCSAndProgCredRaw : Data → Option (CurrencySymbol × Data)
  | Data.List (Data.B dcs :: plcD :: _) => some (dcs, plcD)
  | _ => none

def transferParamsRefIdx : Data → Option Integer
  | Data.Constr 0 (_ :: _ :: _ :: _ :: Data.I p :: _) => some p
  | _ => none

def paramsPublishedBy (ctx : ScriptContext) : Option (CurrencySymbol × Data) :=
  match transferParamsRefIdx ctx.scriptContextRedeemer with
  | none => none
  | some idx =>
      match atIdx idx ctx.scriptContextTxInfo.txInfoReferenceInputs with
      | none => none
      | some i =>
          match i.txInInfoResolved.txOutDatum with
          | .OutputDatum d => paramsDirCSAndProgCredRaw d
          | _ => none

def Contained (base : Credential) (cs : CurrencySymbol) (tn : TokenName)
    (ctx : ScriptContext) : Prop :=
  outSum base cs tn ctx.scriptContextTxInfo.txInfoOutputs
    ≥ inSum base cs tn ctx.scriptContextTxInfo.txInfoInputs
      + _root_.WscDx.mintOf cs tn ctx.scriptContextTxInfo.txInfoMint

end Model

def P1UnshapedFormH (accept : CurrencySymbol → ScriptContext → Prop) : Prop :=
  ∀ (ppCS : CurrencySymbol) (ctx : ScriptContext) (base : Credential)
    (dirCS : CurrencySymbol) (cs : CurrencySymbol) (tn : TokenName),
    validRewardingContext ctx = true →
    Model.paramsPublishedBy ctx = some (dirCS, IsData.toData base) →
    Model.isProgrammable dirCS cs ctx.scriptContextTxInfo.txInfoReferenceInputs = true →
    accept ppCS ctx →
      Model.Contained base cs tn ctx

end WscDx
