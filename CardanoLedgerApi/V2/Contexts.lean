import CardanoLedgerApi.IsData.Class
import CardanoLedgerApi.V1.Contexts
import CardanoLedgerApi.V2.Tx
import PlutusCore

namespace CardanoLedgerApi.V2.Contexts
open IsData.Class
open PlutusCore.Integer (Integer)
open PlutusCore.Data (Data)
open PlutusCore.UPLC.Term (Term)
open Recursors
open V1.Address
open V1.Credential
open V1.Contexts (isKnownCertificate validDatumMap validMintValue validScriptCertificate
                  validSigners validTxOutValue validTxRange validWithdrawals)
open V1.DCert
open V1.Scripts
open V1.Time
open V1.Value
open Tx


/-- An input of a pending transaction -/
structure TxInInfo where
  txInInfoOutRef : TxOutRef
  txInInfoResolved : TxOut
deriving Repr

def beqTxInInfo (x y : TxInInfo) : Bool :=
  x.txInInfoOutRef == y.txInInfoOutRef &&
  x.txInInfoResolved == y.txInInfoResolved

/-- BEq instance for TxInInfo -/
instance : BEq TxInInfo := ⟨beqTxInInfo⟩

/-! DecidableEq instance for TxInInfo -/
theorem beqTxInInfo_imp_eq (x y : TxInInfo) : beqTxInInfo x y → x = y := by
  match x, y with
  | TxInInfo.mk tid1 idx1, TxInInfo.mk tid2 idx2 => simp [beqTxInInfo]

theorem beqTxInInfo_false_imp_not_eq (x y : TxInInfo) : beqTxInInfo x y = false → x ≠ y := by
  match x, y with
  | TxInInfo.mk tid1 idx1, TxInInfo.mk tid2 idx2 => simp [beqTxInInfo]

def TxInInfo.decEq (x y : TxInInfo) : Decidable (Eq x y) :=
  match h:(beqTxInInfo x y) with
  | true => isTrue (beqTxInInfo_imp_eq _ _ h)
  | false => isFalse (beqTxInInfo_false_imp_not_eq _ _ h)

instance : DecidableEq TxInInfo := TxInInfo.decEq

/-! LawfulBEq instance for TxInInfo -/
theorem beqTxInInfo_reflexive (x : TxInInfo) : beqTxInInfo x x = true := by simp [beqTxInInfo]

instance : LawfulBEq TxInInfo where
  eq_of_beq {a b} := (beqTxInInfo_imp_eq a b)
  rfl {bs} := by simp [BEq.beq]; apply beqTxInInfo_reflexive


/-- IsData instance for TxInInfo -/
instance : IsData TxInInfo where
 toData info :=
    mkDataConstr 0
    [ IsData.toData info.txInInfoOutRef
    , IsData.toData info.txInInfoResolved
    ]
 fromData
 | Data.Constr 0 [r_ref, r_out] =>
     match IsData.fromData r_ref with
     | some tref =>
        match IsData.fromData r_out with
        | some out => some ⟨tref, out⟩
        | none => none
     | none => none
 | _ => none

abbrev ScriptPurpose := V1.Contexts.ScriptPurpose

abbrev Withdrawals := List (StakingCredential × Integer) -- handled as a Data.Map at the Data level for V2

/-- Return the list `Data × Data` representation for Withdrawals.
    V1->V2: each element in Withdrawals is encoded as Data × Data.
-/
def txInfoWdrlToListPairData (xs : Withdrawals) : List (Data × Data) :=
  Recursor.map x in xs with (IsData.toData x.1, Data.I x.2)

/-- Try to decode `Withdrawals` from a `Data × Data` list instance. -/
def listPairDataToTxInfoWdrl (xs : List (Data × Data)) : Option Withdrawals :=
  match xs with
  | [] => some []
  | (d1, Data.I i) :: xs' =>
      match IsData.fromData d1, listPairDataToTxInfoWdrl xs' with
      | some cred, some rest => (cred, i) :: rest
      | _, _ => none
  | _ => none

/-- IsData instance for Withdrawals
    V1->V2: is encoded as a Data.Map
-/
instance : IsData Withdrawals where
  toData x := Data.Map (txInfoWdrlToListPairData x)
  fromData
  | Data.Map r_wdrwl => listPairDataToTxInfoWdrl r_wdrwl
  | _ => none

abbrev DatumMap := List (DatumHash × Datum) -- handled as a Data.Map at the Data level for V2

/-- Return the list `Data × Data` representation for DatumMap.
    V1->V2: each element in DatumMap is encoded as a Data × Data.
-/
def txInfoDataToListPairData (xs : DatumMap) : List (Data × Data):=
  Recursor.map x in xs with (Data.B x.1, x.2)

/-- Try to decode DatumMap from a `Data` list instance. -/
def listPairDataToTxInfoData (xs : List (Data × Data)) : Option DatumMap :=
  match xs with
  | [] => some []
  | (Data.B dh, d2) :: xs' =>
      match listPairDataToTxInfoData xs' with
      | some rest => (dh, d2) :: rest
      |  _ => none
  | _ => none

/- IsData instance for DatumMap
   V1->V2: is encoded as a Data.Map
-/
instance : IsData DatumMap where
  toData x := Data.Map (txInfoDataToListPairData x)
  fromData
  | Data.Map r_dmap => listPairDataToTxInfoData r_dmap
  | _ => none

abbrev RedeemerMap := List (ScriptPurpose × Redeemer) -- handled as a Data.Map at the Data level

/-- Return the list `Data × Data` representation for RedeemerMap. -/
def txInfoRedeemersToListPairData (xs : RedeemerMap) : List (Data × Data) :=
  Recursor.map x in xs with (IsData.toData x.1, x.2)

/-- Try to decode `RedeemerMap` from a `Data × Data` list instance. -/
def listPairDataToTxInfoRedeemers (xs : List (Data × Data)) : Option RedeemerMap :=
  match xs with
  | [] => some []
  | (d1, d2) :: xs' =>
      match IsData.fromData d1, listPairDataToTxInfoRedeemers xs' with
      | some purpose, some rest => (purpose, d2) :: rest
      | _, _ => none

/-- IsData instance for RedeemerMap -/
instance : IsData RedeemerMap where
  toData x := Data.Map (txInfoRedeemersToListPairData x)
  fromData
  | Data.Map r_map => listPairDataToTxInfoRedeemers r_map
  | _ => none


/-- A pending transaction. This is the view as seen by scripts -/
structure TxInfo where
  /-- Transaction's inputs: cannot be an empty list. -/
  txInfoInputs : List TxInInfo
  /-- Transaction's reference inputs. -/
  txInfoReferenceInputs : List TxInInfo
  /-- Transaction's outputs -/
  txInfoOutputs : List TxOut
  /-- The fee paid by this transaction. -/
  txInfoFee : Value
  /-- The `Value` minted by this transaction -/
  txInfoMint : Value
  /-- Digests of certificates included in this transaction. -/
  txInfoDCert : List DCert
  /-- Withdrawals -/
  txInfoWdrl : Withdrawals
  /-- The valid range for the transaction. -/
  txInfoValidRange : Data -- keep at Data level
  /-- Signers of the transaction. -/
  txInfoSignatories : List PubKeyHash
  /-- The lookup table for redeemers attached to the transaction. -/
  txInfoRedeemers : RedeemerMap
  /-- The lookup table of datums attached to the transaction. -/
  txInfoData : DatumMap
  /-- ^ Hash of the pending transaction body (i.e. transaction excluding witnesses) -/
  txInfoId : TxId
deriving Repr


def beqTxInfo (x y : TxInfo) : Bool :=
  x.txInfoInputs == y.txInfoInputs &&
  x.txInfoReferenceInputs == y.txInfoReferenceInputs &&
  x.txInfoOutputs == y.txInfoOutputs &&
  x.txInfoFee == y.txInfoFee &&
  x.txInfoMint == y.txInfoMint &&
  x.txInfoDCert == y.txInfoDCert &&
  x.txInfoWdrl == y.txInfoWdrl &&
  x.txInfoValidRange == y.txInfoValidRange &&
  x.txInfoSignatories == y.txInfoSignatories &&
  x.txInfoRedeemers == y.txInfoRedeemers &&
  x.txInfoData == y.txInfoData &&
  x.txInfoId == y.txInfoId

/-- BEq instance for TxInfo -/
instance : BEq TxInfo := ⟨beqTxInfo⟩

/-! DecidableEq instance for TxInfo -/
@[simp] theorem beqTxInfo_iff_eq (x y : TxInfo) : beqTxInfo x y ↔ x = y := by
  match x, y with
  | TxInfo.mk .., TxInfo.mk .. =>
    simp [beqTxInfo]; apply Iff.intro <;>
    . repeat' rw [and_imp];
      intros; repeat' constructor <;> repeat' assumption

@[simp] theorem beqTxInfo_false_iff_not_eq (x y : TxInfo) : beqTxInfo x y = false ↔ x ≠ y := by
  match x, y with
  | TxInfo.mk .., TxInfo.mk .. => simp [beqTxInfo]

def TxInfo.decEq (x y : TxInfo) : Decidable (Eq x y) :=
  match h:(beqTxInfo x y) with
  | true => isTrue ((beqTxInfo_iff_eq _ _).1 h)
  | false => isFalse ((beqTxInfo_false_iff_not_eq _ _).1 h)

instance : DecidableEq TxInfo := TxInfo.decEq

/-! LawfulBEq instance for TxInfo -/
theorem beqTxInfo_reflexive (x : TxInfo) : beqTxInfo x x = true := by
   cases x <;> simp [beqTxInfo]

instance : LawfulBEq TxInfo where
  eq_of_beq {a b} := (beqTxInfo_iff_eq a b).1
  rfl {bs} := by simp [BEq.beq]


/-- Return the `Data` list representation for the given `TxInInfo` list. -/
def txInfoInputsToListData (xs : List TxInInfo) : List Data :=
  Recursor.map x in xs with IsData.toData x

/-- Try to decode `TxInInfo` list from a `Data` list instance. -/
def listDataToTxInfoInputs (xs : List Data) : Option (List TxInInfo) :=
  match xs with
  | [] => some []
  | x :: xs' =>
      match IsData.fromData x, listDataToTxInfoInputs xs' with
      | some tin, some rest => tin :: rest
      | _, _ => none

/-- IsData instance for List TxInInfo -/
instance : IsData (List TxInInfo) where
  toData ins := Data.List (txInfoInputsToListData ins)
  fromData
  | Data.List r_ins => listDataToTxInfoInputs r_ins
  | _ => none

/-- Return the list `Data` representation for the given `TxOut` list. -/
def txInfoOutputsToListData (xs : List TxOut) : List Data :=
  Recursor.map x in xs with IsData.toData x

/-- Try to decode `TxOut` list from a `Data` list instance. -/
def listDataToTxInfoOutputs (xs : List Data) : Option (List TxOut) :=
  match xs with
  | [] => some []
  | x :: xs' =>
      match IsData.fromData x, listDataToTxInfoOutputs xs' with
      | some out, some rest => out :: rest
      | _, _ => none

/-- IsData instance for List TxOut -/
instance : IsData (List TxOut) where
  toData outs := Data.List (txInfoOutputsToListData outs)
  fromData
  | Data.List r_outs => listDataToTxInfoOutputs r_outs
  | _ => none


/-- IsData instance for TxInfo -/
instance : IsData TxInfo where
  toData info :=
    mkDataConstr 0
    [ IsData.toData info.txInfoInputs
    , IsData.toData info.txInfoReferenceInputs
    , IsData.toData info.txInfoOutputs
    , IsData.toData info.txInfoFee
    , IsData.toData info.txInfoMint
    , IsData.toData info.txInfoDCert
    , IsData.toData info.txInfoWdrl
    , IsData.toData info.txInfoValidRange
    , IsData.toData info.txInfoSignatories
    , IsData.toData info.txInfoRedeemers
    , IsData.toData info.txInfoData
    , IsData.toData info.txInfoId
    ]
  fromData
  | Data.Constr 0 [r_ins, r_refs, r_outs, r_fees, r_mint, r_certs, r_wdrwl, r_range, r_sig, r_redeemers, r_dat, r_tid] =>
     match IsData.fromData r_ins, IsData.fromData r_refs, IsData.fromData r_outs,
           IsData.fromData r_fees, IsData.fromData r_mint,
           IsData.fromData r_certs, IsData.fromData r_wdrwl,
           IsData.fromData r_range, IsData.fromData r_sig,
           IsData.fromData r_redeemers, IsData.fromData r_dat, IsData.fromData r_tid with
    | some ins, some refs, some outs, some fees, some mint, some certs,
      some wdrwl, some range, some sigs, some redeemers, some dat, some tid =>
       some ⟨ins, refs, outs, fees, mint, certs, wdrwl, range, sigs, redeemers, dat, tid⟩
    | _, _, _, _, _, _, _, _, _, _, _, _ => none
  | _ => none

/-- The context that the currently-executing script can access. -/
structure ScriptContext where
  scriptContextTxInfo : TxInfo
  scriptContextPurpose : ScriptPurpose
deriving Repr


def beqScriptContext (x y : ScriptContext) : Bool :=
  x.scriptContextTxInfo == y.scriptContextTxInfo &&
  x.scriptContextPurpose == y.scriptContextPurpose

/-- BEq instance for ScriptContext -/
instance : BEq ScriptContext := ⟨beqScriptContext⟩

/-! DecidableEq instance for ScriptContext -/
@[simp] theorem beqScriptContext_iff_eq (x y : ScriptContext) : beqScriptContext x y ↔ x = y := by
  match x, y with
  | ScriptContext.mk .., ScriptContext.mk .. => simp [beqScriptContext]

@[simp] theorem beqScriptContext_false_iff_not_eq (x y : ScriptContext) : beqScriptContext x y = false ↔ x ≠ y := by
  match x, y with
  | ScriptContext.mk .., ScriptContext.mk .. => simp [beqScriptContext]

def ScriptContext.decEq (x y : ScriptContext) : Decidable (Eq x y) :=
  match h:(beqScriptContext x y) with
  | true => isTrue ((beqScriptContext_iff_eq _ _).1 h)
  | false => isFalse ((beqScriptContext_false_iff_not_eq _ _).1 h)

instance : DecidableEq ScriptContext := ScriptContext.decEq

/-! LawfulBEq instance for ScriptContext -/
theorem beqScriptContext_reflexive (x : ScriptContext) : beqScriptContext x x = true := by
   cases x <;> simp [beqScriptContext]

instance : LawfulBEq ScriptContext where
  eq_of_beq {a b} := (beqScriptContext_iff_eq a b).1
  rfl {bs} := by simp [BEq.beq]

/- IsData instance for ScriptContext -/
instance : IsData ScriptContext where
  toData ctx := mkDataConstr 0 [IsData.toData ctx.scriptContextTxInfo, IsData.toData ctx.scriptContextPurpose]
  fromData
  | Data.Constr 0 [r_infos, r_purpose] =>
      match IsData.fromData r_infos, IsData.fromData r_purpose with
      | some infos, some purpose => some ⟨infos, purpose⟩
      | _, _ => none
  | _ => none

/-- Input for spending validator. -/
structure SpendingInput where
  datum : Datum
  redeemer : Redeemer
  ctx : ScriptContext
deriving Repr

def beqSpendingInput (x y : SpendingInput) : Bool :=
  x.datum == y.datum &&
  x.redeemer == y.redeemer &&
  x.ctx == y.ctx

/-- BEq instance for SpendingInput -/
instance : BEq SpendingInput := ⟨beqSpendingInput⟩

/-! DecidableEq instance for SpendingInput -/
@[simp] theorem beqSpendingInput_iff_eq (x y : SpendingInput) : beqSpendingInput x y ↔ x = y := by
  match x, y with
  | SpendingInput.mk .., SpendingInput.mk .. =>
    simp [beqSpendingInput]; apply Iff.intro <;>
    . repeat' rw [and_imp];
      intros; repeat' constructor <;> repeat' assumption

@[simp] theorem beqSpendingInput_false_iff_not_eq (x y : SpendingInput) : beqSpendingInput x y = false ↔ x ≠ y := by
  match x, y with
  | SpendingInput.mk .., SpendingInput.mk .. => simp [beqSpendingInput]

def SpendingInput.decEq (x y : SpendingInput) : Decidable (Eq x y) :=
  match h:(beqSpendingInput x y) with
  | true => isTrue ((beqSpendingInput_iff_eq _ _).1 h)
  | false => isFalse ((beqSpendingInput_false_iff_not_eq _ _).1 h)

instance : DecidableEq SpendingInput := SpendingInput.decEq


/-- Input for minting validator. -/
structure MintingInput where
  redeemer : Redeemer
  ctx : ScriptContext
deriving Repr

def beqMintingInput (x y : MintingInput) : Bool :=
  x.redeemer == y.redeemer &&
  x.ctx == y.ctx

/-- BEq instance for MintingInput -/
instance : BEq MintingInput := ⟨beqMintingInput⟩

/-! DecidableEq instance for MintingInput -/
@[simp] theorem beqMintingInput_iff_eq (x y : MintingInput) : beqMintingInput x y ↔ x = y := by
  match x, y with
  | MintingInput.mk .., MintingInput.mk .. => simp [beqMintingInput];

@[simp] theorem beqMintingInput_false_iff_not_eq (x y : MintingInput) : beqMintingInput x y = false ↔ x ≠ y := by
  match x, y with
  | MintingInput.mk .., MintingInput.mk .. => simp [beqMintingInput]

def MintingInput.decEq (x y : MintingInput) : Decidable (Eq x y) :=
  match h:(beqMintingInput x y) with
  | true => isTrue ((beqMintingInput_iff_eq _ _).1 h)
  | false => isFalse ((beqMintingInput_false_iff_not_eq _ _).1 h)

instance : DecidableEq MintingInput := MintingInput.decEq

/-- Input for rewarding validator. -/
structure RewardingInput where
  redeemer : Redeemer
  ctx : ScriptContext
deriving Repr

def beqRewardingInput (x y : RewardingInput) : Bool :=
  x.redeemer == y.redeemer &&
  x.ctx == y.ctx

/-- BEq instance for RewardingInput -/
instance : BEq RewardingInput := ⟨beqRewardingInput⟩

/-! DecidableEq instance for RewardingInput -/
@[simp] theorem beqRewardingInput_iff_eq (x y : RewardingInput) : beqRewardingInput x y ↔ x = y := by
  match x, y with
  | RewardingInput.mk .., RewardingInput.mk .. => simp [beqRewardingInput];

@[simp] theorem beqRewardingInput_false_iff_not_eq (x y : RewardingInput) : beqRewardingInput x y = false ↔ x ≠ y := by
  match x, y with
  | RewardingInput.mk .., RewardingInput.mk .. => simp [beqRewardingInput]

def RewardingInput.decEq (x y : RewardingInput) : Decidable (Eq x y) :=
  match h:(beqRewardingInput x y) with
  | true => isTrue ((beqRewardingInput_iff_eq _ _).1 h)
  | false => isFalse ((beqRewardingInput_false_iff_not_eq _ _).1 h)

instance : DecidableEq RewardingInput := RewardingInput.decEq


/-- Input for certifying validator. -/
structure CertifyingInput where
  redeemer : Redeemer
  ctx : ScriptContext
deriving Repr

def beqCertifyingInput (x y : CertifyingInput) : Bool :=
  x.redeemer == y.redeemer &&
  x.ctx == y.ctx

/-- BEq instance for CertifyingInput -/
instance : BEq CertifyingInput := ⟨beqCertifyingInput⟩

/-! DecidableEq instance for CertifyingInput -/
@[simp] theorem beqCertifyingInput_iff_eq (x y : CertifyingInput) : beqCertifyingInput x y ↔ x = y := by
  match x, y with
  | CertifyingInput.mk .., CertifyingInput.mk .. => simp [beqCertifyingInput];

@[simp] theorem beqCertifyingInput_false_iff_not_eq (x y : CertifyingInput) : beqCertifyingInput x y = false ↔ x ≠ y := by
  match x, y with
  | CertifyingInput.mk .., CertifyingInput.mk .. => simp [beqCertifyingInput]

def CertifyingInput.decEq (x y : CertifyingInput) : Decidable (Eq x y) :=
  match h:(beqCertifyingInput x y) with
  | true => isTrue ((beqCertifyingInput_iff_eq _ _).1 h)
  | false => isFalse ((beqCertifyingInput_false_iff_not_eq _ _).1 h)

instance : DecidableEq CertifyingInput := CertifyingInput.decEq

/-! Helpers -/

/-- Find the `TxInInfo` corresponding to the given `TxOutRef` in a list of inputs. -/
def resolveInput (utxo : TxOutRef) (inputs : List TxInInfo) : Option TxInInfo :=
  Recursor.findMap? x in inputs => x.txInInfoOutRef == utxo with x

/-- Find the spending script's own input and return the corresponding `TxInInfo`, if present.
    Return `none` when script purpose is not `Spending`.
-/
def findOwnInput (ctx : ScriptContext) : Option TxInInfo :=
  match ctx.scriptContextPurpose with
  | .Spending ownTxOutRef => resolveInput ownTxOutRef ctx.scriptContextTxInfo.txInfoInputs
  | _ => none

/-- Find a datum by its hash, if present in the witness map. -/
def findDatum (dh : DatumHash) (datums : DatumMap) : Option Datum :=
  Recursor.findMap? x in datums => x.1 == dh with x.2

/-- Find a hash of a datum, if present in the witness map. -/
def findDatumHash (dat : Datum) (datums : DatumMap) : Option DatumHash :=
  Recursor.findMap? x in datums => x.2 == dat with x.1

/-- Find all inputs associated to the given public key hash. -/
def findPubKeyInputs (pk : PubKeyHash) (inputs : List TxInInfo) : List TxInInfo :=
  Recursor.findAll x in inputs => hasPubKeyAddress pk x.txInInfoResolved

/-- Find all inputs associated to the given script hash. -/
def findScriptInputs (sh : ScriptHash) (inputs : List TxInInfo) : List TxInInfo :=
  Recursor.findAll x in inputs => hasScriptAddress sh x.txInInfoResolved

/-- Find all outputs associated to the given public key hash. -/
def findPubKeyOutputs (pk : PubKeyHash) (outputs : List TxOut) : List TxOut :=
  Recursor.findAll x in outputs => hasPubKeyAddress pk x

/-- Find all outputs associated to the given script hash. -/
def findScriptOutputs (sh : ScriptHash) (outputs : List TxOut) : List TxOut :=
  Recursor.findAll x in outputs => hasScriptAddress sh x

/-- Return the first input satisfying predicate f, if present. -/
def findInput (f : TxInInfo → Bool) (inputs : List TxInInfo) : Option TxInInfo :=
  Recursor.find? x in inputs => f x

/-- Return the first output satisfying predicate f, if present. -/
def findOutput (f : TxOut → Bool) (outputs : List TxOut) : Option TxOut :=
  Recursor.find? x in outputs => f x

/-- Find a redeemer according to the given script purpose, if present in the redeemer map. -/
def findRedeemer (purpose : ScriptPurpose) (redeemers : RedeemerMap) : Option Redeemer :=
  Recursor.findMap? x in redeemers => x.1 == purpose with x.2

/-- Return the `CurrencySymbol` of the current validator script only when script purpose is `Minting`. -/
def ownCurrencySymbol (ctx : ScriptContext) : Option CurrencySymbol :=
  match ctx.scriptContextPurpose with
  | .Minting cs => some cs
  | _ => none


/-- Return the total value of inputs spent in the pending transaction -/
def valueSpent (ctx : ScriptContext) : Value :=
  let rec visit (ins : List TxInInfo) (acc : Value) : Value :=
    match ins with
    | [] => acc
    | x :: xs => visit xs (merge x.txInInfoResolved.txOutValue acc)
  visit ctx.scriptContextTxInfo.txInfoInputs null


/-- Return the total value of inputs produced by the pending transaction -/
def valueProduced (ctx : ScriptContext) : Value :=
  let rec visit (outs : List TxOut) (acc : Value) : Value :=
    match outs with
    | [] => acc
    | x :: xs => visit xs (merge x.txOutValue acc)
  visit ctx.scriptContextTxInfo.txInfoOutputs null

/-- Return the list of arguments to be applied to a UPLC Spending validator -/
def spendingInputs (input : SpendingInput) : List Term :=
  [toTerm input.datum, toTerm input.redeemer, toTerm input.ctx]

/-- Return the list of arguments to be applied to a UPLC Minting validator -/
def mintingInputs (input : MintingInput) : List Term :=
  [toTerm input.redeemer, toTerm input.ctx]

/-- Return the list of arguments to be applied to a UPLC Rewarding validator -/
def rewardingInputs (input : RewardingInput) : List Term :=
  [toTerm input.redeemer, toTerm input.ctx]

/-- Return the list of arguments to be applied to a UPLC Certifying validator -/
def certifyingInputs (input : CertifyingInput) : List Term :=
  [toTerm input.redeemer, toTerm input.ctx]


/-! Predicates -/

/-- Return `true` only when the script purpose is `Minting`. -/
def isMintingPurpose (ctx : ScriptContext) : Bool :=
  match ctx.scriptContextPurpose with
  | .Minting _ => true
  | _ => false

/-- Return `true` only when the script purpose is `Rewarding`. -/
def isRewardingPurpose (ctx : ScriptContext) : Bool :=
  match ctx.scriptContextPurpose with
  | .Rewarding _  => true
  | _ => false

/-- Return `true` only when the script purpose is `Spending`. -/
def isSpendingPurpose (ctx : ScriptContext) : Bool :=
  match ctx.scriptContextPurpose with
  | .Spending _  => true
  | _ => false

/-- Return `true` only when the script purpose is `Certifying`. -/
def isCertifyingPurpose (ctx : ScriptContext) : Bool :=
  match ctx.scriptContextPurpose with
  | .Certifying _  => true
  | _ => false

/-- Check if the given `TxOutRef` is present in the list of inputs. -/
def utxoConsumed (utxo : TxOutRef) (inputs : List TxInInfo) : Bool :=
  Recursor.any x in inputs => x.txInInfoOutRef == utxo

/-- Check if a transaction was signed by the given public key hash. -/
def txSignedBy (pk : PubKeyHash) (tx : TxInfo) : Bool :=
  Recursor.any x in tx.txInfoSignatories => x == pk

/-- Check if the given public key hash is the only signatory. -/
def onlySingedBy (pk : PubKeyHash) (tx : TxInfo) : Bool :=
  tx.txInfoSignatories == [pk]

/-- Check if the given staking credential is present in the withdrawal map. -/
def credentialInWithdrawals (stk : StakingCredential) (withdrawals : Withdrawals) : Bool :=
  Recursor.any x in withdrawals => x.1 == stk


/-- [LEDGER-RULE]: Ledger rules for datum applied to the current spending script (V2).
     The datum applied to the spending script is valid if and only if the following
     conditions are satisfied:

     1. Datum or datum hash present at the script's resolved input:
         - hasDatum ownResolvedInput

     2. txOutInlineDatum ownResolvedInput = some datum' → datum = datum'

     3. txOutDatumHash ownResolvedInput = some dh' → (dh', datum) ∈ ctx.scriptContextTxInfo.txInfoData

     with:
       - datum : corresponding to the input datum applied to the current spending script.
       - ownResolvedInput : corresponding to the resolved input `TxOut` for the current spending script.
       - ctx : corresponding to the ScriptContext applied to the current spending script.
-/
def validInputDatum (datum : Datum) (ownResolvedInput : TxOut) (ctx : ScriptContext) : Bool :=
  match ownResolvedInput.txOutDatum with
  | .OutputDatum datum' => datum' == datum
  | .OutputDatumHash dh => findDatum dh ctx.scriptContextTxInfo.txInfoData == some datum
  | .NoOutputDatum => false

/-- [LEDGER-RULE]: Ledger rules for ScriptPurpose (V2):
     ScriptPurpose `s` is valid if and only if the following conditions are satisfied:

     1. (s, redeemer) ∈ ctx.scriptContextTxInfo.txInfoRedeemers

     2. s = Spending ownTxOutRef →
          ∃ x ∈ ctx.scriptContextTxInfo.txInfoInputs,
             x.txInInfoOutRef = ownTxOutRef ∧
             isScriptCredentialAddress x.txInInfoResolved.txOutAddress ∧
             validInputDatum datum x.txInInfoResolved ctx

     3. s = Minting cs → hasCurrencySymbol cs ctx.scriptContextTxInfo.txInfoMint

     4. s = Rewarding cred →
          isStakingScriptCredential cred ∧
          ∃ n : Integer, (cred, n) ∈ ctx.scriptContextTxInfo.txInfoWdrl

     5. s = Certifying cert →
              validScriptCertificate cert ∧
              cert ∈ ctx.scriptContextTxInfo.txInfoDCert

     with:
       - datum : corresponding to the input datum applied to the current spending script, if any.
       - redeemer : corresponding to the input redeemer applied to the current validator script.
       - ctx : corresponding to the ScriptContext applied to the current validator script.
-/
def validScriptPurpose (optDatum : Option Datum) (redeemer : Redeemer) (ctx : ScriptContext) : Bool :=
  let validPurpose :=
    match ctx.scriptContextPurpose, optDatum  with
    | .Spending ownTxOutRef, some datum =>
         if let some tin := resolveInput ownTxOutRef ctx.scriptContextTxInfo.txInfoInputs
         then isScriptCredentialAddress tin.txInInfoResolved.txOutAddress &&
              validInputDatum datum tin.txInInfoResolved ctx
         else false
    | .Minting cs, none => hasCurrencySymbol cs ctx.scriptContextTxInfo.txInfoMint
    | .Rewarding cred, none =>
          isStakingScriptCredential cred &&
          credentialInWithdrawals cred ctx.scriptContextTxInfo.txInfoWdrl
    | .Certifying cert, none =>
           validScriptCertificate cert ∧
           isKnownCertificate cert ctx.scriptContextTxInfo.txInfoDCert
    | _, _ => false
  findRedeemer ctx.scriptContextPurpose ctx.scriptContextTxInfo.txInfoRedeemers == some redeemer &&
  validPurpose


/-- [LEDGER-RULE]: Ledger rules for a single transaction input (V2):
    An input `tin` is valid if and only if the following is satisfied:
      - validTxOutValue tin.txInInfoResolved.txOutValue ∧
        ( isScriptCredentialAddress tin.txInInfoResolved.txOutAddress →
            hasDatum tin.txInInfoResolved ∧
            ( txOutDatumHash tin.TxInInfoResolved = some dh →
               ∃ (dat : Datum), (dh, dat) ∈ ctx.scriptContextTxInfo.txInfoData )
        )
    NOTE: For V2, any spending script must have either a datum or a datum hash.
    If the spending script has a datum hash a corresponding entry in the witness map must exists.
-/
def validTxInInfo (tin : TxInInfo) (ctx : ScriptContext) : Bool :=
  let validScriptTxInInfo (out : TxOut) : Bool :=
    match out.txOutAddress.addressCredential, out.txOutDatum with
    | .ScriptCredential _, .OutputDatum _ => true
    | .ScriptCredential _, .OutputDatumHash dh => (findDatum dh ctx.scriptContextTxInfo.txInfoData).isSome
    | .ScriptCredential _, _ => false
    | _, _ => true
  validTxOutValue tin.txInInfoResolved.txOutValue &&
  validScriptTxInInfo tin.txInInfoResolved

/-- [LEDGER-RULE]: Ledger rules for transaction's inputs (V2):
      Let ctx.scriptContextTxInfo.txInfoInputs = [in₁, in₂ ..., inₘ],
      the transaction's inputs are valid if and only if the following conditions are satisfied:
        1. Transaction has at least one input, i.e.,  m ≥ 1

        2. Inputs are sorted according to `TxOutRef`
            - in₁.txInInfoOutRef < in₂.txInInfoOutRef < .. < inₘ.txInInfoOutRef

        3. ∀ i ∈ [1..m],
             validTxOutValue inᵢ.txInInfoResolved.txOutValue ∧
             ( isScriptCredentialAddress inᵢ.txInInfoResolved.txOutAddress →
               hasDatum inᵢ.txInInfoResolved ∧
               ( txOutDatumHash inᵢ.TxInInfoResolved = some dh →
                  ∃ (dat : Datum), (dh, dat) ∈ ctx.scriptContextTxInfo.txInfoData )
             )
     with:
       - ctx : corresponding to the ScriptContext applied to the current validator script.

     NOTE: For V2, any spending script must have either a datum or a datum hash.
     If the spending script has a datum hash then, a corresponding entry in the witness map must exists.
-/
def validInputs (ctx : ScriptContext) : Bool :=
  let rec visit (ins : List TxInInfo) (prevTxOutRef : TxOutRef) : Bool :=
    match ins with
    | [] => true
    | x :: xs' => prevTxOutRef < x.txInInfoOutRef && validTxInInfo x ctx && visit xs' x.txInInfoOutRef
  match ctx.scriptContextTxInfo.txInfoInputs with
  | [] => false -- at least one input expected
  | x :: xs => validTxInInfo x ctx && visit xs x.txInInfoOutRef



/-- [LEDGER-RULE]: Ledger rules for a single transaction's reference input (V2):
    An reference input `tin` is valid if and only if the following is satisfied:
      - validTxOutValue tin.txInInfoResolved.txOutValue ∧
        ( isScriptCredentialAddress tin.txInInfoResolved.txOutAddress → hasDatum tin.txInInfoResolved )
    NOTE: For V2, any spending script must have either a datum or a datum hash.
    NOTE: When a utxo for a spending script is present in the reference input list,
           if the utxo has a datum hash, a corresponding entry in the witness map is not mandatory.
-/
def validReferenceInput (tin : TxInInfo) : Bool :=
  validTxOutValue tin.txInInfoResolved.txOutValue &&
  (!(isScriptCredentialAddress tin.txInInfoResolved.txOutAddress) || hasDatum tin.txInInfoResolved)


/-- [LEDGER-RULE]: Ledger rules for transaction's reference inputs (V2):
    The transaction's reference inputs are valid if and only if one of following conditions is satisfied:
      1. Reference input list is empty
           - ctx.scriptContextTxInfo.txInfoReferenceInputs = []

      2. Reference input list is not empty such that:
          2.1 ctx.scriptContextTxInfo.txInfoReferenceInputs = [in₁, in₂ ..., inₘ]

          2.2 Reference Inputs are sorted according to `TxOutRef`
               - in₁.txInInfoOutRef < in₂.txInInfoOutRef < .. < inₘ.txInInfoOutRef

          2.3. ∀ i ∈ [1..m],
                 validTxOutValue inᵢ.txInInfoResolved.txOutValue ∧
                 ( isScriptCredentialAddress inᵢ.txInInfoResolved.txOutAddress → hasDatum inᵢ.txInInfoResolved )
     with:
       - ctx : corresponding to the ScriptContext applied to the current validator script.

     NOTE: For V2, any spending script must have either a datum or a datum hash.
     NOTE: When a utxo for a spending script is present in the reference input list,
           if the utxo has a datum hash, a corresponding entry in the witness map is not mandatory.
-/
def validReferenceInputs (ctx : ScriptContext) : Bool :=
  let rec visit (references : List TxInInfo) (prevTxOutRef : TxOutRef) : Bool :=
    match references with
    | [] => true
    | x :: xs' => prevTxOutRef < x.txInInfoOutRef && validReferenceInput x  && visit xs' x.txInInfoOutRef
  match ctx.scriptContextTxInfo.txInfoReferenceInputs with
  | [] => true
  | x :: xs => validReferenceInput x && visit xs x.txInInfoOutRef


/-- [LEDGER-RULE]: Ledger rules for transaction's outputs (V2):
      - ∀ x ∈ ctx.scriptContextTxInfo.txInfoOutputs,
           validTxOutValue x.txOutValue ∧
           (isScriptCredentialAddress x.txOutAddress → hasDatum x)
     with:
       - ctx : corresponding to the ScriptContext applied to the current validator script.

     NOTE: It's not mandatory for a datum hash in a transaction's output to be present in
     the witness map (even for script address).
     NOTE: For V2, a utxo created at a script address must have either a datum or a datum hash.
-/
def validOutputs (outputs : List TxOut) : Bool :=
  Recursor.all x in outputs =>
     validTxOutValue x.txOutValue &&
     (!(isScriptCredentialAddress x.txOutAddress) || hasDatum x)


/-- [LEDGER-RULE]: Ledger rules for transaction's redeemer map.
    The redeemer map is valid if and only if one of the following conditions is satisfied:
      1. Redeemer map is empty
          - ctx.scriptContextTxInfo.txInfoRedeemers = []
      2. Redeemer map is sorted w.r.t. ScriptPurpose
          ctx.scriptContextTxInfo.txInfoRedeemers = [(sp₁, redeemer₁), ..., (spₙ, redeemerₙ)] ∧
          sp₁ < sp₂ < .. < spₙ
-/
def validRedeemerMap (redeemers : RedeemerMap) : Bool :=
  let rec visit (redeemers : RedeemerMap) (prev_sp : ScriptPurpose) : Bool :=
   match redeemers with
   | [] => true
   | x :: xs => prev_sp < x.1 && visit xs x.1
  match redeemers with
  | [] => true
  | x :: xs => visit xs x.1


/-- [LEDGER-RULE]: A V2 pending transaction is balanced if and only if:
      - Value in inputs + txInfoMint = Value in outputs + txInfoFees
-/
def isBalanced (ctx : ScriptContext) : Bool :=
  let sv := valueSpent ctx
  let pv := valueProduced ctx
  lovelaceOf sv = lovelaceOf pv + lovelaceOf ctx.scriptContextTxInfo.txInfoFee &&
  withoutLovelace (merge sv ctx.scriptContextTxInfo.txInfoMint) == withoutLovelace pv


/-- [LEDGER-RULE]: Ledger rules for a pending transaction (V2):
    1. All transaction's inputs are valid, i.e.,
        - validInputs ctx

    2. All transaction's reference inputs are valid, i.e.,
        - validReferenceInputs ctx

    3. All transaction's outputs are valid, i.e.,
        - validOutputs ctx.scriptContextTxInfo.txInfoOutputs

    4. ctx.txInfoFees only has non-zero Ada.

    5. Minted value is valid, i.e,
         - validMintValue ctx.scriptContextTxInfo.txInfoMint

    6. Withdrawal list is sorted w.r.t. StakingCredential
         - validWithdrawals ctx.scriptContextTxInfo.txInfoWdrl

    7. Validity range cannot be empty
        - ¬ isEmpty ctx.scriptContextTxInfo.txInfoValidRange

    8. List of signatories is sorted w.r.t. PubKeyHash
         - validSigners ctx.scriptContextTxInfo.txInfoSignatories

    9. RedeemerMap is sorted w.r.t. ScriptPurpose
         - validRedeemerMap ctx.scriptContextTxInfo.txInfoRedeemers

    10. DatumMap is sorted w.r.t.DatumHash
         - validDatumMap ctx.scriptContextTxInfo.txInfoData

    11. Transaction is balanced, i.e.,
        - Value in inputs + txInfoMint = Value in outputs + txInfoFees
-/
def validTxInfo (ctx : ScriptContext) : Bool :=
  validInputs ctx &&
  validReferenceInputs ctx &&
  validOutputs ctx.scriptContextTxInfo.txInfoOutputs &&
  hasOnlyNonZeroAda ctx.scriptContextTxInfo.txInfoFee &&
  validMintValue ctx.scriptContextTxInfo.txInfoMint &&
  validWithdrawals ctx.scriptContextTxInfo.txInfoWdrl &&
  validTxRange ctx.scriptContextTxInfo.txInfoValidRange &&
  validSigners ctx.scriptContextTxInfo.txInfoSignatories &&
  validRedeemerMap ctx.scriptContextTxInfo.txInfoRedeemers &&
  validDatumMap ctx.scriptContextTxInfo.txInfoData &&
  isBalanced ctx


/-- [LEDGER-RULE]: Ledger rules for ScriptContext (V2):
    A ScriptContext ctx is valid if and only if the following conditions are satisfied:
    1. ScriptPurpose is valid, i.e.,
        - validScriptPurpose datum redeemer ctx

    2. The pending transaction is valid, i.e.,
        - validTxInfo ctx

    with:
       - datum : corresponding to the input datum applied to the current spending script, if any.
       - redeemer : corresponding to the input redeemer applied to the current validator script.
       - ctx : corresponding to the ScriptContext applied to the current validator script.
-/
def validScriptContext (datum : Option Datum) (redeemer : Redeemer) (ctx : ScriptContext) : Bool :=
  validScriptPurpose datum redeemer ctx &&
  validTxInfo ctx


/-- Check ledger rule for spending script context -/
def validSpendingContext (input : SpendingInput) : Bool :=
  validScriptContext (some input.datum) input.redeemer input.ctx

/-- Check ledger rule for minting script context -/
def validMintingContext (input : MintingInput) : Bool :=
  validScriptContext none input.redeemer input.ctx

/-- Check ledger rule for rewarding script context -/
def validRewardingContext (input : RewardingInput) : Bool :=
  validScriptContext none input.redeemer input.ctx

/-- Check ledger rule for certifying script context -/
def validCertifyingContext (input : CertifyingInput) : Bool :=
  validScriptContext none input.redeemer input.ctx


end CardanoLedgerApi.V2.Contexts
