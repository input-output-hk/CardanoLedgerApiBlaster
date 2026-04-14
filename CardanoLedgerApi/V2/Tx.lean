import CardanoLedgerApi.IsData.Class
import CardanoLedgerApi.V1.Tx
import PlutusCore

namespace CardanoLedgerApi.V2.Tx

open IsData.Class
open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)
open V1.Address
open V1.Credential
open V1.Scripts
open V1.Value

abbrev TxId := V1.Tx.TxId
abbrev TxOutRef := V1.Tx.TxOutRef

/-- The datum attached to an output:
        either nothing;
        a datum hash;
        or the datum itself (an "inline datum").
-/
inductive OutputDatum where
  | NoOutputDatum : OutputDatum
  | OutputDatumHash : DatumHash → OutputDatum
  | OutputDatum : Datum → OutputDatum
deriving Repr

def beqOutputDatum (x y : OutputDatum) : Bool :=
  match x, y with
  | .NoOutputDatum, .NoOutputDatum => true
  | .OutputDatumHash dh1, .OutputDatumHash dh2 => dh1 == dh2
  | .OutputDatum d1, .OutputDatum d2 => d1 == d2
  | _, _=> false

/-- BEq instance for OutputDatum -/
instance : BEq OutputDatum := ⟨beqOutputDatum⟩

/-! DecidableEq instance for OutputDatum -/
@[simp] theorem beqOutputDatum_iff_eq (x y : OutputDatum) : beqOutputDatum x y ↔ x = y := by
  cases x <;> cases y <;> simp [beqOutputDatum]

@[simp] theorem beqOutputDatum_false_iff_not_eq (x y : OutputDatum) : beqOutputDatum x y = false ↔ x ≠ y := by
  cases x <;> cases y <;> simp [beqOutputDatum]

def decEqOutputDatum (x y : OutputDatum) : Decidable (Eq x y) :=
  match h:(beqOutputDatum x y) with
  | true => isTrue ((beqOutputDatum_iff_eq _ _).1 h)
  | false => isFalse ((beqOutputDatum_false_iff_not_eq _ _).1 h)

instance : DecidableEq OutputDatum := decEqOutputDatum

/-! LawfulBEq instance for OutputDatum -/
theorem beqOutputDatum_reflexive (x : OutputDatum) : beqOutputDatum x x = true := by
   cases x <;> simp [beqOutputDatum]

instance : LawfulBEq OutputDatum where
  eq_of_beq {a b} := (beqOutputDatum_iff_eq a b).1
  rfl {bs} := by simp [BEq.beq]

/-- IsData instance for OutputDatum -/
instance : IsData OutputDatum where
 toData
 | .NoOutputDatum => mkDataConstr 0 []
 | .OutputDatumHash dh => mkDataConstr 1 [Data.B dh]
 | .OutputDatum d =>  mkDataConstr 2 [d]
 fromData
 | Data.Constr 0 [] => some .NoOutputDatum
 | Data.Constr 1 [Data.B dh] => some (.OutputDatumHash dh)
 | Data.Constr 2 [d] => some (.OutputDatum d)
 | _ => none


/-- A transaction output, consisting of an `Address`, a `Value`, optionally a `Datum/DatumHash`
    and optionally a reference script.
-/
structure TxOut where
  txOutAddress : Address
  txOutValue : Value
  txOutDatum : OutputDatum
  txOutReferenceScript : Option ScriptHash
 deriving Repr

def beqTxOut (x y : TxOut) : Bool :=
  x.txOutAddress == y.txOutAddress &&
  x.txOutValue == y.txOutValue &&
  x.txOutDatum == y.txOutDatum &&
  x.txOutReferenceScript == y.txOutReferenceScript

/-- BEq instance for TxOut -/
instance : BEq TxOut := ⟨beqTxOut⟩

/-! DecidableEq instance for TxOut -/
@[simp] theorem beqTxOut_iff_eq (x y : TxOut) : beqTxOut x y ↔ x = y := by
  match x, y with
  | TxOut.mk .., TxOut.mk .. =>
      simp [beqTxOut]; apply Iff.intro <;>
      . repeat' rw [and_imp];
        intros; repeat' constructor <;> repeat' assumption


@[simp] theorem beqTxOut_false_iff_not_eq (x y : TxOut) : beqTxOut x y = false ↔ x ≠ y := by
  match x, y with
  | TxOut.mk .., TxOut.mk .. => simp [beqTxOut];

def TxOut.decEq (x y : TxOut) : Decidable (Eq x y) :=
  match h:(beqTxOut x y) with
  | true => isTrue ((beqTxOut_iff_eq _ _).1 h)
  | false => isFalse ((beqTxOut_false_iff_not_eq _ _).1 h)

instance : DecidableEq TxOut := TxOut.decEq

/-! LawfulBEq instance for TxOut -/
theorem beqTxOut_reflexive (x : TxOut) : beqTxOut x x = true := by simp [beqTxOut]

instance : LawfulBEq TxOut where
  eq_of_beq {a b} := (beqTxOut_iff_eq a b).1
  rfl {bs} := by simp [BEq.beq]


/-- IsData instance for TxOut -/
instance : IsData TxOut where
  toData out :=
     mkDataConstr 0
     [ IsData.toData out.txOutAddress
     , IsData.toData out.txOutValue
     , IsData.toData out.txOutDatum
     , IsData.toData out.txOutReferenceScript
     ]
  fromData
  | Data.Constr 0 [r_addr, r_val, r_dat, r_scr] =>
      match IsData.fromData r_addr, IsData.fromData r_val, IsData.fromData r_dat, IsData.fromData r_scr with
      | some addr, some val, some dat, some scr => some ⟨addr, val, dat, scr⟩
      | _, _, _, _ => none
  | _ => none


/-! List of helpers and predicates -/

/-- Return the public key hash attached to a `TxOut`, if any. -/
def txOutPubKey (out : TxOut) : Option PubKeyHash :=
  toPubKeyHash out.txOutAddress

/-- Return the script hash attached to a `TxOut`, if any. -/
def txOutScriptHash (out : TxOut) : Option ScriptHash :=
  toScriptHash out.txOutAddress

/-- Return the inline datum attached to a `TxOut`, if any. -/
def txOutInlineDatum (out : TxOut) : Option Datum :=
  match out.txOutDatum with
  | .OutputDatum d => some d
  | _ => none

/-- Return the datum hash  attached to a `TxOut`, if any. -/
def txOutDatumHash (out : TxOut) : Option DatumHash :=
  match out.txOutDatum with
  | .OutputDatumHash dh => some dh
  | _ => none


/-- Return `true` only when `TxOut.txOutAddress` corresponds to validator hash `sh`. -/
def hasScriptAddress (sh : ScriptHash) (out : TxOut) : Bool :=
  hasScriptHash sh out.txOutAddress

/-- Return `true` only when `TxOut.txOutAddress` corresponds to public key hash `pk`. -/
def hasPubKeyAddress (pk : PubKeyHash) (out : TxOut) : Bool :=
  hasPubKeyHash pk out.txOutAddress

/-- Return `true` only when `TxOut` has a datum hash or an inline datum. -/
def hasDatum (out : TxOut) : Bool :=
  match out.txOutDatum with
  | .NoOutputDatum => false
  | _ => true

/-- Return `true` only when `TxOut` has a datum hash. -/
def hasDatumHash (out : TxOut) : Bool :=
  match out.txOutDatum with
  | .OutputDatumHash _ => true
  | _ => false

/-- Check if `TxOut` has a reference script. -/
def hasReferenceScript (out : TxOut) : Bool :=
  out.txOutReferenceScript.isSome

end CardanoLedgerApi.V2.Tx
