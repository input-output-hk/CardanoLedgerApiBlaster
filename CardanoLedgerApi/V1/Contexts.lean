import CardanoLedgerApi.IsData.Class
import CardanoLedgerApi.V1.Address
import CardanoLedgerApi.V1.Credential
import CardanoLedgerApi.V1.DCert
import CardanoLedgerApi.V1.Time
import CardanoLedgerApi.Recursors
import CardanoLedgerApi.V1.Scripts
import CardanoLedgerApi.V1.Tx
import CardanoLedgerApi.V1.Value
import PlutusCore

namespace CardanoLedgerApi.V1.Contexts
open Address
open Credential
open DCert
open IsData.Class
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.Data (Data)
open PlutusCore.UPLC.Term (Term)
open Recursors
open Scripts
open Tx
open Time
open Value

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

/--  Purpose of the script that is currently running -/
inductive ScriptPurpose where
  | Minting : CurrencySymbol → ScriptPurpose
  | Spending : TxOutRef → ScriptPurpose
  | Rewarding : StakingCredential → ScriptPurpose
  | Certifying : DCert → ScriptPurpose
deriving Repr


def beqScriptPurpose (x y : ScriptPurpose) : Bool :=
  match x, y with
  | .Minting cs1, .Minting cs2 => cs1 == cs2
  | .Spending ref1, .Spending ref2 => ref1 == ref2
  | .Rewarding cred1, .Rewarding cred2 => cred1 == cred2
  | .Certifying cert1, .Certifying cert2 => cert1 == cert2
  | _, _=> false

/-- BEq instance for ScriptPurpose -/
instance : BEq ScriptPurpose := ⟨beqScriptPurpose⟩

/-! DecidableEq instance for ScriptPurpose -/
@[simp] theorem beqScriptPurpose_iff_eq (x y : ScriptPurpose) : beqScriptPurpose x y ↔ x = y := by
  cases x <;> cases y <;> simp [beqScriptPurpose]

@[simp] theorem beqScriptPurpose_false_iff_not_eq (x y : ScriptPurpose) : beqScriptPurpose x y = false ↔ x ≠ y := by
  cases x <;> cases y <;> simp [beqScriptPurpose]

def ScriptPurpose.decEq (x y : ScriptPurpose) : Decidable (Eq x y) :=
  match h:(beqScriptPurpose x y) with
  | true => isTrue ((beqScriptPurpose_iff_eq _ _).1 h)
  | false => isFalse ((beqScriptPurpose_false_iff_not_eq _ _).1 h)

instance : DecidableEq ScriptPurpose := ScriptPurpose.decEq

/-! LawfulBEq instance for ScriptPurpose -/
theorem beqScriptPurpose_reflexive (x : ScriptPurpose) : beqScriptPurpose x x = true := by
   cases x <;> simp [beqScriptPurpose]

instance : LawfulBEq ScriptPurpose where
  eq_of_beq {a b} := (beqScriptPurpose_iff_eq a b).1
  rfl {bs} := by simp [BEq.beq]


def ltScriptPurpose (x y : ScriptPurpose) : Bool :=
  match x, y with
  | .Minting cs1, .Minting cs2 => cs1 < cs2
  | .Minting _, _ => true
  | .Spending tref1, .Spending tref2 => tref1 < tref2
  | .Spending _, .Minting _ => false
  | .Spending _, _ => true
  | .Rewarding cred1, .Rewarding cred2 => cred1 < cred2
  | .Rewarding _, .Minting _
  | .Rewarding _, .Spending _ => false
  | .Rewarding _, _ => true
  | .Certifying cert1, .Certifying cert2 => cert1 < cert2
  | .Certifying _, _ => false

/-- LT instance for ScriptPurpose -/
instance : LT ScriptPurpose where
  lt x y := ltScriptPurpose x y

/-! DecidableLT instance for ScriptPurpose -/
theorem ltScriptPurpose_true_imp_lt (x y : ScriptPurpose) : ltScriptPurpose x y → x < y := by
  cases x <;> cases y <;> simp only [ltScriptPurpose, LT.lt] <;> simp

theorem ltScriptPurpose_false_imp_not_lt (x y : ScriptPurpose) :
  ltScriptPurpose x y = false → ¬ x < y := by
    cases x <;> cases y <;> simp only [ltScriptPurpose, LT.lt] <;> simp

def ScriptPurpose.decLt (x y : ScriptPurpose) : Decidable (LT.lt x y) :=
  match h:(ltScriptPurpose x y) with
  | true => isTrue (ltScriptPurpose_true_imp_lt _ _ h)
  | false => isFalse (ltScriptPurpose_false_imp_not_lt _ _ h)

instance : DecidableLT ScriptPurpose := ScriptPurpose.decLt

/-! Std.Irrefl instance for ScriptPurpose -/
@[simp] theorem ltScriptPurpose_same_false (x : ScriptPurpose) : ltScriptPurpose x x = false := by
    cases x <;> simp only [ltScriptPurpose, LT.lt] <;> simp <;> apply String.le_refl

theorem ScriptPurpose.lt_irrefl (x : ScriptPurpose) : ¬ x < x := by cases x <;> simp [LT.lt]

instance : Std.Irrefl (. < . : ScriptPurpose → ScriptPurpose → Prop) where
  irrefl := ScriptPurpose.lt_irrefl

/-- LE instance for ScriptPurpose -/
instance : LE ScriptPurpose where
  le x y := ¬ (y < x)

/-! DecidableLE instance for ScriptPurpose -/
instance : DecidableLE ScriptPurpose :=
  fun x y => inferInstanceAs (Decidable (¬ (y < x)))

/-- IsData instance for ScriptPurpose -/
instance : IsData ScriptPurpose where
  toData
  | .Minting cs => mkDataConstr 0 [IsData.toData cs]
  | .Spending ref => mkDataConstr 1 [IsData.toData ref]
  | .Rewarding cred => mkDataConstr 2 [IsData.toData cred]
  | .Certifying cert => mkDataConstr 3 [IsData.toData cert]
  fromData
  | Data.Constr 0 [Data.B cs] => some (.Minting cs)
  | Data.Constr 1 [r_ref] =>
       match IsData.fromData r_ref with
       | some ref => some (.Spending ref)
       | none => none
  | Data.Constr 2 [r_cred] =>
       match IsData.fromData r_cred with
       | some cred => some (.Rewarding cred)
       | none => none
  | Data.Constr 3 [r_cert] =>
       match IsData.fromData r_cert with
       | some cert => some (.Certifying cert)
       | none => none
  | _ => none

abbrev Withdrawals := List (StakingCredential × Integer)

/- IsData instance for StakingCredential × Integer -/
instance : IsData (StakingCredential × Integer) where
  toData x := mkDataConstr 0 [IsData.toData x.1, Data.I x.2]
  fromData
  | Data.Constr 0 [r_cred, Data.I i] =>
      match IsData.fromData r_cred with
      | some cred => some (cred, i)
      | none => none
  | _ => none

/-- Return the list `Data` representation for Withdrawals. -/
def txInfoWdrlToListData (xs : Withdrawals) : List Data :=
  Recursor.map x in xs with IsData.toData x

/-- Try to decode `Withdrawals` from a `Data` list instance. -/
def listDataToTxInfoWdrl (xs : List Data) : Option Withdrawals :=
  match xs with
  | [] => some []
  | x :: xs' =>
      match IsData.fromData x, listDataToTxInfoWdrl xs' with
      | some cred, some rest => cred :: rest
      | _, _ => none

/-- IsData instance for Withdrawals -/
instance : IsData Withdrawals where
  toData x := Data.List (txInfoWdrlToListData x)
  fromData
  | Data.List r_wdrwl => listDataToTxInfoWdrl r_wdrwl
  | _ => none

abbrev DatumMap := List (DatumHash × Datum)

/- IsData instance for DatumHash × Datum -/
instance : IsData (DatumHash × Datum) where
  toData x := mkDataConstr 0 [Data.B x.1, x.2]
  fromData
  | Data.Constr 0 [Data.B dh, dat] => some (dh, dat)
  | _ => none

/-- Return the list `Data` representation for DatumMap. -/
def txInfoDataToListData (xs : DatumMap) : List Data :=
  Recursor.map x in xs with IsData.toData x

/-- Try to decode DatumMap from a `Data` list instance. -/
def listDataToTxInfoData (xs : List Data) : Option DatumMap :=
  match xs with
  | [] => some []
  | x :: xs' =>
      match IsData.fromData x, listDataToTxInfoData xs' with
      | some d, some rest => d :: rest
      | _, _ => none

/- IsData instance for DatumMap -/
instance : IsData DatumMap where
  toData x := Data.List (txInfoDataToListData x)
  fromData
  | Data.List r_dmap => listDataToTxInfoData r_dmap
  | _ => none


/-- A pending transaction. This is the view as seen by scripts -/
structure TxInfo where
  /-- Transaction's inputs: cannot be an empty list. -/
  txInfoInputs : List TxInInfo
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
  /-- The lookup table of datums attached to the transaction. -/
  txInfoData : DatumMap
  /-- ^ Hash of the pending transaction body (i.e. transaction excluding witnesses) -/
  txInfoId : TxId
deriving Repr


def beqTxInfo (x y : TxInfo) : Bool :=
  x.txInfoInputs == y.txInfoInputs &&
  x.txInfoOutputs == y.txInfoOutputs &&
  x.txInfoFee == y.txInfoFee &&
  x.txInfoMint == y.txInfoMint &&
  x.txInfoDCert == y.txInfoDCert &&
  x.txInfoWdrl == y.txInfoWdrl &&
  x.txInfoValidRange == y.txInfoValidRange &&
  x.txInfoSignatories == y.txInfoSignatories &&
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

/-- Return the list `Data` representation for the given `DCert` list. -/
def txInfoDCertsToListData (xs : List DCert) : List Data :=
  Recursor.map x in xs with IsData.toData x

/-- Try to decode `DCert` list from a `Data` list instance. -/
def listDataToTxInfoDCerts (xs : List Data) : Option (List DCert) :=
  match xs with
  | [] => some []
  | x :: xs' =>
      match IsData.fromData x, listDataToTxInfoDCerts xs' with
      | some out, some rest => out :: rest
      | _, _ => none

/-- IsData instance for List DCert -/
instance : IsData (List DCert) where
  toData certs := Data.List (txInfoDCertsToListData certs)
  fromData
  | Data.List r_certs => listDataToTxInfoDCerts r_certs
  | _ => none



/-- Return the list `Data` representation for signatories. -/
def txInfoSignatoriesToListData (xs : List PubKeyHash) : List Data :=
  Recursor.map x in xs with Data.B x

/-- Try to decode signatories from a `Data` list instance. -/
def listDataToTxInfoSignatories (xs : List Data) : Option (List PubKeyHash) :=
  match xs with
  | [] => some []
  | Data.B pk :: xs' =>
      match listDataToTxInfoSignatories xs' with
      | some rest => pk :: rest
      | none => none
  | _ => none

/-- IsData instance for List PubKeyHash -/
instance : IsData (List PubKeyHash) where
  toData x := Data.List (txInfoSignatoriesToListData x)
  fromData
  | Data.List r_sig =>  listDataToTxInfoSignatories r_sig
  | _ => none


/-- IsData instance for TxInfo -/
instance : IsData TxInfo where
  toData info :=
    mkDataConstr 0
    [ IsData.toData info.txInfoInputs
    , IsData.toData info.txInfoOutputs
    , IsData.toData info.txInfoFee
    , IsData.toData info.txInfoMint
    , IsData.toData info.txInfoDCert
    , IsData.toData info.txInfoWdrl
    , IsData.toData info.txInfoValidRange
    , IsData.toData info.txInfoSignatories
    , IsData.toData info.txInfoData
    , IsData.toData info.txInfoId
    ]
  fromData
  | Data.Constr 0 [r_ins, r_outs, r_fees, r_mint, r_certs, r_wdrwl, r_range, r_sig, r_dat, r_tid] =>
     match IsData.fromData r_ins, IsData.fromData r_outs,
           IsData.fromData r_fees, IsData.fromData r_mint,
           IsData.fromData r_certs, IsData.fromData r_wdrwl,
           IsData.fromData r_range, IsData.fromData r_sig,
           IsData.fromData r_dat, IsData.fromData r_tid with
    | some ins, some outs, some fees, some mint, some certs, some wdrwl, some range, some sigs, some dat, some tid =>
       some ⟨ins, outs, fees, mint, certs, wdrwl, range, sigs, dat, tid⟩
    | _, _, _, _, _, _, _, _, _, _ => none
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

/-- Check if the given certificate is present in the `DCert` list. -/
def isKnownCertificate (cert : DCert) (certificates : List DCert) : Bool :=
  Recursor.any x in certificates => x == cert

/-- [LEDGER-RULE]: Ledger rules for Value in TxOut (V1):
    A Value `v` is valid if and only if it has the form
     v = [ (cs₀, [(tn₀, n₀)]),
           (cs₁ [(tn₍₁₎₍₁₎, n₍₁₎₍₁₎), ..., (tn₍₁₎₍ₖ₁₎, n₍₁₎₍ₖ₁₎)]), ...,
           (csₘ [(tn₍ₘ₎₍₁₎, n₍ₘ₎₍₁₎), ..., (tn₍₁₎₍ₖₘ₎, n₍₁₎₍ₖₘ₎)]) ]

     such that:
       1. First currency is positive Ada (i.e., min ada value) :
          - cs₀ = "" ∧ tn₀ = "" ∧ n₀ > 0

       2. All currency symbols are sorted
          - cs₉ < cs₁ < cs₂ < ... < csₘ

       3. ∀ i ∈ [1..m], csᵢ has at least one token such that:
           - kᵢ ≥ 1 ∧
           - tn₍ᵢ₎₍₁₎ < tn₍ᵢ₎₍₂₎ < ... < tn₍ᵢ₎₍ₖᵢ₎ (i.e., token names are sorted)
           - ∀ j ∈ [1..kᵢ], n₍ᵢ₎₍ⱼ₎ > 0 (i.e., only positive quantity)
-/
def validTxOutValue (v : Value) : Bool :=
  let rec validTokens (tns : List (Data × Data)) (prev_tn : ByteString) : Bool :=
    match tns with
    | [] => true
    | (Data.B tn, Data.I n) :: xs => prev_tn < tn && n > 0 && validTokens xs tn
    | _ => false
  let rec validCurrencySymbol (v : Value) (prev_cs : ByteString) : Bool :=
    match v with
    | [] => true
    | (Data.B cs, Data.Map ((Data.B tn, Data.I n) :: tokens)) :: xs =>
         prev_cs < cs && n > 0 && validTokens tokens tn && validCurrencySymbol xs cs
    | _ => false
  match v with
  | (Data.B "", Data.Map [(Data.B "", Data.I n)]) :: xs =>
       n > 0 && validCurrencySymbol xs ""
  | _ => false


/-- [LEDGER-RULE]: Ledger rules for Value in TxInfoMint (V1):
    A Value `v` is valid if and only if it has the form
     v = [ (cs₀, [(tn₀, n₀)]),
           (cs₁ [(tn₍₁₎₍₁₎, n₍₁₎₍₁₎), ..., (tn₍₁₎₍ₖ₁₎, n₍₁₎₍ₖ₁₎)]), ...,
           (csₘ [(tn₍ₘ₎₍₁₎, n₍ₘ₎₍₁₎), ..., (tn₍₁₎₍ₖₘ₎, n₍₁₎₍ₖₘ₎)]) ]

     such that:
       1. First currency is zero Ada:
          - cs₀ = "" ∧ tn₀ = "" ∧ n₀ = 0

       2. All currency symbols are sorted
          - cs₉ < cs₁ < cs₂ < ... < csₘ

       3. ∀ i ∈ [1..m], csᵢ has at least one token such that:
           - kᵢ ≥ 1 ∧
           - tn₍ᵢ₎₍₁₎ < tn₍ᵢ₎₍₂₎ < ... < tn₍ᵢ₎₍ₖᵢ₎ (i.e., token names are sorted)
           - ∀ j ∈ [1..kᵢ], n₍ᵢ₎₍ⱼ₎ ≠ 0 (i.e., not null quantity)
-/
def validMintValue (v : Value) : Bool :=
  let rec validMintTokens (tns : List (Data × Data)) (prev_tn : ByteString) : Bool :=
    match tns with
    | [] => true
    | (Data.B tn, Data.I n) :: xs => prev_tn < tn && n != 0 && validMintTokens xs tn
    | _ => false
  let rec validCurrencySymbol (v : Value) (prev_cs : ByteString) : Bool :=
    match v with
    | [] => true
    | (Data.B cs, Data.Map ((Data.B tn, Data.I n) :: tokens)) :: xs =>
         prev_cs < cs && n != 0 && validMintTokens tokens tn && validCurrencySymbol xs cs
    | _ => false
  match v with
  | (Data.B "", Data.Map [(Data.B "", Data.I n)]) :: xs =>
       n == 0 && validCurrencySymbol xs ""
  | _ => false

/-- [LEDGER-RULE]: Ledger rules for the certificate of current certifying script (V1).
    The certificate `cerf` is valid if and only if one of the following conditions is satisfied:

    1. cert = DCertDelegRegKey cred ∧ isStakingScriptCredential cred

    2. cert = DCertDelegDeRegKey cred ∧ isStakingScriptCredential cred

    3. cert = DCertDelegDelegate cred pk ∧ isStakingScriptCredential cred
-/
def validScriptCertificate (cert : DCert) : Bool :=
  match cert with
  | .DCertDelegRegKey cred
  | .DCertDelegDeRegKey cred
  | .DCertDelegDelegate cred _ => isStakingScriptCredential cred
  | _ => false

/-- [LEDGER-RULE]: Ledger rules for ScriptPurpose (V1):
     ScriptPurpose `s` is valid if and only if the following conditions are satisfied:
     1. s = Spending ownTxOutRef →
          ∃ x ∈ ctx.scriptContextTxInfo.txInfoInputs,
             x.txInInfoOutRef = ownTxOutRef ∧
             isScriptCredentialAddress x.txInInfoResolved.txOutAddress ∧
             ∃ (dh, dat) ∈ ctx.scriptContextTxInfo.txInfoData,
               x.txInInfoResolved.txOutDatumHash = some dh ∧
               dat = datum

     2. s = Minting cs → hasCurrencySymbol cs ctx.scriptContextTxInfo.txInfoMint

     3. s = Rewarding cred →
          isStakingScriptCredential cred ∧
          ∃ n : Integer, (cred, n) ∈ ctx.scriptContextTxInfo.txInfoWdrl

     4. s = Certifying cert →
             validScriptCertificate cert ∧
             cert ∈ ctx.scriptContextTxInfo.txInfoDCert

     with:
       - datum : corresponding to the input datum applied to the current spending script, if any.
       - ctx : corresponding to the ScriptContext applied to the current validator script.
-/
def validScriptPurpose (input : Option Datum) (ctx : ScriptContext) : Bool :=
  match ctx.scriptContextPurpose, input  with
  | .Spending ownTxOutRef, some datum =>
         if let some tin := resolveInput ownTxOutRef ctx.scriptContextTxInfo.txInfoInputs
         then
           let dh := findDatumHash datum ctx.scriptContextTxInfo.txInfoData
           isScriptCredentialAddress tin.txInInfoResolved.txOutAddress && dh.isSome &&
           tin.txInInfoResolved.txOutDatumHash == dh
         else false
  | .Minting cs, none => hasCurrencySymbol cs ctx.scriptContextTxInfo.txInfoMint
  | .Rewarding cred, none =>
       isStakingScriptCredential cred &&
       credentialInWithdrawals cred ctx.scriptContextTxInfo.txInfoWdrl
  | .Certifying cert, none =>
         validScriptCertificate cert &&
         isKnownCertificate cert ctx.scriptContextTxInfo.txInfoDCert
  | _, _ => false


/-- [LEDGER-RULE]: Ledger rules for a single transaction input (V1):
    An input `tin` is valid if and only if the following is satisfied:
      - validTxOutValue tin.txInInfoResolved.txOutValue ∧
        ( isScriptCredentialAddress tin.txInInfoResolved.txOutAddress →
            ∃ (dh, dat) ∈ ctx.scriptContextTxInfo.txInfoData,
               tin.txInInfoResolved.txOutDatumHash = some dh
        )
    NOTE: For V1, any spending script must have a datum hash entry in the witness map.
-/
def validTxInInfo (tin : TxInInfo) (ctx : ScriptContext) : Bool :=
  let validScriptTxInInfo (out : TxOut) : Bool :=
    match out.txOutAddress.addressCredential, out.txOutDatumHash with
    | .ScriptCredential _, some dh => (findDatum dh ctx.scriptContextTxInfo.txInfoData).isSome
    | .ScriptCredential _, _ => false
    | _, _ => true
  validTxOutValue tin.txInInfoResolved.txOutValue &&
  validScriptTxInInfo tin.txInInfoResolved

/-- [LEDGER-RULE]: Ledger rules for transaction's inputs (V1):
      Let ctx.scriptContextTxInfo.txInfoInputs = [in₁, in₂ ..., inₘ],
      the transaction's inputs are valid if and only if the following conditions are satisfied:
        1. Transaction has at least one input, i.e.,  m ≥ 1

        2. Inputs are sorted according to `TxOutRef`
            - in₁.txInInfoOutRef < in₂.txInInfoOutRef < .. < inₘ.txInInfoOutRef

        3. ∀ i ∈ [1..m],
             validTxOutValue inᵢ.txInInfoResolved.txOutValue ∧
             ( isScriptCredentialAddress inᵢ.txInInfoResolved.txOutAddress →
                ∃ (dh, dat) ∈ ctx.scriptContextTxInfo.txInfoData,
                  inᵢ.txInInfoResolved.txOutDatumHash = some dh
             )
     with:
       - ctx : corresponding to the ScriptContext applied to the current validator script.

     NOTE: For V1, any spending script must have a datum hash entry in the witness map.
-/
def validInputs (ctx : ScriptContext) : Bool :=
  let rec visit (ins : List TxInInfo) (prevTxOutRef : TxOutRef) : Bool :=
    match ins with
    | [] => true
    | x :: xs' => prevTxOutRef < x.txInInfoOutRef && validTxInInfo x ctx && visit xs' x.txInInfoOutRef
  match ctx.scriptContextTxInfo.txInfoInputs with
  | [] => false -- at least one input expected
  | x :: xs => validTxInInfo x ctx && visit xs x.txInInfoOutRef


/-- [LEDGER-RULE]: Ledger rules for transaction's outputs (V1):
      - ∀ x ∈ ctx.scriptContextTxInfo.txInfoOutputs,
           validTxOutValue x.txOutValue ∧
           (isScriptCredentialAddress x.txOutAddress → hasDatumHash x)
     with:
       - ctx : corresponding to the ScriptContext applied to the current validator script.

     NOTE: It's not mandatory for a datum hash in a transaction's output to be present in
     the witness map (even for script address).
-/
def validOutputs (outputs : List TxOut) : Bool :=
  Recursor.all x in outputs =>
     validTxOutValue x.txOutValue &&
     (!(isScriptCredentialAddress x.txOutAddress) || hasDatumHash x)

/-- [LEDGER-RULE]: Ledger rules for transaction's Withdrawals.
    The withdrawal map is valid if and only if one of the following conditions is satisfied:
      1. Withdrawal map is empty
          - ctx.scriptContextTxInfo.txInfoWdrl = []
      2. Withdrawal map is sorted w.r.t. StakingCredential
          ctx.scriptContextTxInfo.txInfoWdrl = [(cred₁, n₁), ..., (credₖ, nₖ)] ∧
          cred₁ < cred₂ < .. < credₖ
-/
def validWithdrawals (withdrawals : Withdrawals) : Bool :=
  let rec visit (withdrawals : Withdrawals) (prev_cred : StakingCredential) : Bool :=
   match withdrawals with
   | [] => true
   | x :: xs => prev_cred < x.1 && visit xs x.1
  match withdrawals with
  | [] => true
  | x :: xs => visit xs x.1

/-- [LEDGER-RULE]: Ledger rule for transaction's valid range:
     Valid range cannot be empty, i.e.,
       - ¬ isEmpty ctx.scriptContextTxInfo.txInfoValidRange
-/
def validTxRange (r_range : Data) : Bool :=
  match IsData.fromData r_range with
  | some range => !(isEmpty range)
  | none => false

/-- [LEDGER-RULE]: Ledger rules for transaction's signers.
    The transaction's signers list is valid if and only if one of the following conditions is satisfied:
      1. Signers list is empty
          - ctx.scriptContextTxInfo.txInfoSignatories = []
      2. Signers list is sorted
          ctx.scriptContextTxInfo.txInfoSignatories = [pk₁, ..., pkₙ] ∧
          pk₁ < pk₂ < .. < pkₙ
-/
def validSigners (signers : List PubKeyHash) : Bool :=
  let rec visit (signers : List PubKeyHash) (prev_pk : PubKeyHash) : Bool :=
   match signers with
   | [] => true
   | x :: xs => prev_pk < x && visit xs x
  match signers with
  | [] => true
  | x :: xs => visit xs x


/-- [LEDGER-RULE]: Ledger rules for transaction's witness map.
    The witness map is valid if and only if one of the following conditions is satisfied:
      1. Witness map is empty
          - ctx.scriptContextTxInfo.txInfoData = []
      2. Witness map is sorted w.r.t. DatumHash
          ctx.scriptContextTxInfo.txInfoData = [(dh₁, dat₁), ..., (dhₙ, datₙ)] ∧
          dh₁ < dh₂ < .. < dhₙ
-/
def validDatumMap (datums : DatumMap) : Bool :=
  let rec visit (datums : DatumMap) (prev_dh : DatumHash) : Bool :=
   match datums with
   | [] => true
   | x :: xs => prev_dh < x.1 && visit xs x.1
  match datums with
  | [] => true
  | x :: xs => visit xs x.1


/-- [LEDGER-RULE]: A V1 pending transaction is balanced if and only if:
      - Value in inputs + txInfoMint = Value in outputs + txInfoFees
-/
def isBalanced (ctx : ScriptContext) : Bool :=
  let sv := valueSpent ctx
  let pv := valueProduced ctx
  lovelaceOf sv = lovelaceOf pv + lovelaceOf ctx.scriptContextTxInfo.txInfoFee &&
  withoutLovelace (merge sv ctx.scriptContextTxInfo.txInfoMint) == withoutLovelace pv

/-- [LEDGER-RULE]: Ledger rules for a pending transaction (V1):
    1. All transaction's inputs are valid, i.e.,
        - validInputs ctx

    2. All transaction's outputs are valid, i.e.,
        - validOutputs ctx.scriptContextTxInfo.txInfoOutputs

    3. ctx.txInfoFees only has non-zero Ada.

    4. Minted value is valid, i.e,
         - validMintValue ctx.scriptContextTxInfo.txInfoMint

    5. Withdrawal list is sorted w.r.t. StakingCredential
         - validWithdrawals ctx.scriptContextTxInfo.txInfoWdrl

    6. Validity range cannot be empty
        - ¬ isEmpty ctx.scriptContextTxInfo.txInfoValidRange

    7. List of signatories is sorted w.r.t. PubKeyHash
         - validSigners ctx.scriptContextTxInfo.txInfoSignatories

    8. DatumMap is sorted w.r.t. DatumHash
         - validDatumMap ctx.scriptContextTxInfo.txInfoData

    9. Transaction is balanced, i.e.,
        - Value in inputs + txInfoMint = Value in outputs + txInfoFees
-/
def validTxInfo (ctx : ScriptContext) : Bool :=
  validInputs ctx &&
  validOutputs ctx.scriptContextTxInfo.txInfoOutputs &&
  hasOnlyNonZeroAda ctx.scriptContextTxInfo.txInfoFee &&
  validMintValue ctx.scriptContextTxInfo.txInfoMint &&
  validWithdrawals ctx.scriptContextTxInfo.txInfoWdrl &&
  validTxRange ctx.scriptContextTxInfo.txInfoValidRange &&
  validSigners ctx.scriptContextTxInfo.txInfoSignatories &&
  validDatumMap ctx.scriptContextTxInfo.txInfoData &&
  isBalanced ctx


/-- [LEDGER-RULE]: Ledger rules for ScriptContext (V1):
    A ScriptContext ctx is valid if and only if the following conditions are satisfied:
    1. ScriptPurpose is valid, i.e.,
        - validScriptPurpose datum ctx

    2. The pending transaction is valid, i.e.,
        - validTxInfo ctx

    with:
       - datum : corresponding to the input datum applied to the current spending script, if any.
       - ctx : corresponding to the ScriptContext applied to the current validator script.
-/
def validScriptContext (datum : Option Datum) (ctx : ScriptContext) : Bool :=
  validScriptPurpose datum ctx &&
  validTxInfo ctx

/-- Check ledger rule for spending script context -/
def validSpendingContext (input : SpendingInput) : Bool :=
  validScriptContext (some input.datum) input.ctx

/-- Check ledger rule for minting script context -/
def validMintingContext (input : MintingInput) : Bool :=
  validScriptContext none input.ctx

/-- Check ledger rule for rewarding script context -/
def validRewardingContext (input : RewardingInput) : Bool :=
  validScriptContext none input.ctx

/-- Check ledger rule for certifying script context -/
def validCertifyingContext (input : CertifyingInput) : Bool :=
  validScriptContext none input.ctx

end CardanoLedgerApi.V1.Contexts
