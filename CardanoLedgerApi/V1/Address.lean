import CardanoLedgerApi.IsData.Class
import CardanoLedgerApi.V1.Credential
import CardanoLedgerApi.V1.Scripts

import PlutusCore

namespace CardanoLedgerApi.V1.Address
open Credential
open IsData.Class
open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)
open Scripts

/-- The address that should be targeted by a transaction output -/
structure Address where
  addressCredential : Credential
  addressStakingCredential : Option StakingCredential
deriving Repr


def beqAddress (x y : Address) : Bool :=
    x.addressCredential == y.addressCredential &&
    x.addressStakingCredential == y.addressStakingCredential

/-- BEq instance for Address -/
instance : BEq Address := ⟨beqAddress⟩

/-! DecidableEq instance for Address -/
@[simp] theorem beqAddress_iff_eq (x y : Address) : beqAddress x y ↔ x = y := by
  match x, y with
  | Address.mk .., Address.mk .. => simp [beqAddress]

@[simp] theorem beqAddress_false_iff_not_eq (x y : Address) : beqAddress x y = false ↔ x ≠ y := by
  match x, y with
  | Address.mk .., Address.mk .. => simp [beqAddress]

def Address.decEq (x y : Address) : Decidable (Eq x y) :=
  match h:(beqAddress x y) with
  | true => isTrue ((beqAddress_iff_eq _ _).1 h)
  | false => isFalse ((beqAddress_false_iff_not_eq _ _).1 h)

instance : DecidableEq Address := Address.decEq

/-! LawfulBEq instance for Address -/
theorem beqAddress_reflexive (x : Address) : beqAddress x x = true := by simp [beqAddress]

instance : LawfulBEq Address where
  eq_of_beq {a b} := (beqAddress_iff_eq a b).1
  rfl {bs} := by simp [BEq.beq]


/-- IsData instance for Address -/
instance : IsData Address where
  toData addr := mkDataConstr 0 [IsData.toData addr.addressCredential, IsData.toData addr.addressStakingCredential]
  fromData
  | Data.Constr 0 [r_cred, r_stake] =>
     match IsData.fromData r_cred, IsData.fromData r_stake with
     | some cred, some staking => some ⟨cred, staking⟩
     | _, _ => none
  | _ => none


/-! List of helpers and predicates -/

/-- Return the public key hash of the address, if any. -/
def toPubKeyHash (addr : Address) : Option PubKeyHash :=
  match addr.addressCredential with
  | .PubKeyCredential pk => some pk
  | _ => none

/-- Return the validator hash of the address, if any. -/
def toScriptHash (addr : Address) : Option ScriptHash :=
  match addr.addressCredential with
  | .ScriptCredential sh => some sh
  | _ => none


/-- Return `true` only when `addr.addressCredential` corresponds to validator hash `sh`. -/
def hasScriptHash (sh : ScriptHash) (addr : Address) : Bool :=
  hasScriptCredential sh addr.addressCredential

/-- Return `true` only when `addr.addressCredential` corresponds to public key hash `pk`. -/
def hasPubKeyHash (pk : PubKeyHash) (addr : Address) : Bool :=
  hasPubKeyCredential pk addr.addressCredential

/-- Return `true` only when `addr.addressCredential` corresponds a script credential. -/
def isScriptCredentialAddress (addr : Address) : Bool :=
    match addr.addressCredential with
    | .ScriptCredential _ => true
    | _ => false

/-- Return `true` only when `addr.addressCredential` corresponds to public key credential. -/
def isPubKeyCredentialAddress (addr : Address) : Bool :=
    match addr.addressCredential with
    | .PubKeyCredential _=> true
    | _ => false


end CardanoLedgerApi.V1.Address
