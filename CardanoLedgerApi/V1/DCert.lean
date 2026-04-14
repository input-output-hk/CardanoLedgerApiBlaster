import CardanoLedgerApi.IsData.Class
import CardanoLedgerApi.V1.Credential
import PlutusCore

namespace CardanoLedgerApi.V1.DCert
open Credential
open IsData.Class
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)

/-- A representation of the ledger DCert. -/
inductive DCert where
  | DCertDelegRegKey : StakingCredential → DCert
  | DCertDelegDeRegKey : StakingCredential → DCert
  | DCertDelegDelegate : StakingCredential → PubKeyHash → DCert
  | DCertPoolRegister : PubKeyHash → PubKeyHash → DCert
  | DCertPoolRetire : PubKeyHash → Integer → DCert
  | DCertGenesis : DCert
  | DCertMir : DCert
deriving Repr

def beqDCert (x y : DCert) : Bool :=
  match x, y with
  | .DCertDelegRegKey cred1, .DCertDelegRegKey cred2
  | .DCertDelegDeRegKey cred1, .DCertDelegDeRegKey cred2 => cred1 == cred2
  | .DCertDelegDelegate cred1 pk1, .DCertDelegDelegate cred2 pk2 => cred1 == cred2 && pk1 == pk2
  | .DCertPoolRegister pk1 pk2, .DCertPoolRegister pk1' pk2' => pk1 == pk1' &&  pk2 == pk2'
  | .DCertPoolRetire pk1 idx1, .DCertPoolRetire pk2 idx2 => pk1 == pk2 && idx1 == idx2
  | .DCertGenesis, .DCertGenesis
  | .DCertMir, .DCertMir => true
  | _, _ => false

/-- BEq instance for DCert -/
instance : BEq DCert := ⟨beqDCert⟩

/-! DecidableEq instance for DCert -/
@[simp] theorem beqDCert_iff_eq (x y : DCert) : beqDCert x y ↔ x = y := by
  cases x <;> cases y <;> simp [beqDCert]

@[simp] theorem beqDCert_false_iff_not_eq (x y : DCert) : beqDCert x y = false ↔ x ≠ y := by
  cases x <;> cases y <;> simp [beqDCert]

def DCert.decEq (x y : DCert) : Decidable (Eq x y) :=
  match h:(beqDCert x y) with
  | true => isTrue ((beqDCert_iff_eq _ _).1 h)
  | false => isFalse ((beqDCert_false_iff_not_eq _ _).1 h)

instance : DecidableEq DCert := DCert.decEq

/-! LawfulBEq instance for DCert -/
theorem beqDCert_reflexive (x : DCert) : beqDCert x x = true := by
   cases x <;> simp [beqDCert]

instance : LawfulBEq DCert where
  eq_of_beq {a b} := (beqDCert_iff_eq a b).1
  rfl {bs} := by simp [BEq.beq]


def ltDCert (x y : DCert) : Bool :=
  match x, y with
  | .DCertDelegRegKey cred1, .DCertDelegRegKey cred2 => cred1 < cred2
  | .DCertDelegRegKey _, _ => true
  | .DCertDelegDeRegKey cred1, .DCertDelegDeRegKey cred2 => cred1 < cred2
  | .DCertDelegDeRegKey _, .DCertDelegRegKey _ => false
  | .DCertDelegDeRegKey _, _ => true
  | .DCertDelegDelegate cred1 pk1, .DCertDelegDelegate cred2 pk2 =>
        cred1 < cred2 || (cred1 == cred2 && pk1 < pk2)
  | .DCertDelegDelegate .., .DCertDelegRegKey _
  | .DCertDelegDelegate .., .DCertDelegDeRegKey _ => false
  | .DCertDelegDelegate .., _ => true
  | .DCertPoolRegister pk1 pk2, .DCertPoolRegister pk1' pk2' =>
        pk1 < pk1' || (pk1 == pk1' && pk2 < pk2')
  | .DCertPoolRegister .., .DCertDelegRegKey _
  | .DCertPoolRegister .., .DCertDelegDeRegKey _
  | .DCertPoolRegister .., .DCertDelegDelegate .. => false
  | .DCertPoolRegister .., _ => true
  | .DCertPoolRetire pk1 n1, .DCertPoolRetire pk2 n2 =>
       pk1 < pk2 || (pk1 == pk2 && n1 < n2)
  | .DCertPoolRetire .., .DCertDelegRegKey _
  | .DCertPoolRetire .., .DCertDelegDeRegKey _
  | .DCertPoolRetire .., .DCertDelegDelegate ..
  | .DCertPoolRetire ..,  .DCertPoolRegister .. => false
  | .DCertPoolRetire ..,  _ => true
  | .DCertGenesis, .DCertMir => true
  | .DCertGenesis, _ => false
  | .DCertMir, _ => false

/-- LT instance for DCert -/
instance : LT DCert where
  lt x y := ltDCert x y

/-! DecidableLT instance for DCert -/
theorem ltDCert_true_imp_lt (x y : DCert) : ltDCert x y → x < y := by
  cases x <;> cases y <;> simp only [ltDCert, LT.lt] <;> simp

theorem ltDCert_false_imp_not_lt (x y : DCert) :
  ltDCert x y = false → ¬ x < y := by
    cases x <;> cases y <;> simp only [ltDCert, LT.lt] <;> simp

def DCert.decLt (x y : DCert) : Decidable (LT.lt x y) :=
  match h:(ltDCert x y) with
  | true => isTrue (ltDCert_true_imp_lt _ _ h)
  | false => isFalse (ltDCert_false_imp_not_lt _ _ h)

instance : DecidableLT DCert := DCert.decLt

/-! Std.Irrefl instance for DCert -/
@[simp] theorem ltDCert_same_false (x : DCert) : ltDCert x x = false := by
    cases x <;> simp only [ltDCert, LT.lt] <;> simp <;> try constructor <;>
    repeat' apply String.le_refl
    apply String.le_refl
    apply Int.lt_irrefl

theorem DCert.lt_irrefl (x : DCert) : ¬ x < x := by cases x <;> simp [LT.lt]

instance : Std.Irrefl (. < . : DCert → DCert → Prop) where
  irrefl := DCert.lt_irrefl

/-- LE instance for DCert -/
instance : LE DCert where
  le x y := ¬ (y < x)

/-! DecidableLE instance for DCert -/
instance : DecidableLE DCert :=
  fun x y => inferInstanceAs (Decidable (¬ (y < x)))


/-- IsData instance for DCert -/
instance : IsData DCert where
  toData
  | .DCertDelegRegKey cred => mkDataConstr 0 [IsData.toData cred]
  | .DCertDelegDeRegKey cred => mkDataConstr 1 [IsData.toData cred]
  | .DCertDelegDelegate cred pk => mkDataConstr 2 [IsData.toData cred, IsData.toData pk]
  | .DCertPoolRegister pk1 pk2 => mkDataConstr 3 [IsData.toData pk1, IsData.toData pk2]
  | .DCertPoolRetire pk idx => mkDataConstr 4 [IsData.toData pk, IsData.toData idx]
  | .DCertGenesis => mkDataConstr 5
  | .DCertMir => mkDataConstr 6
  fromData
  | Data.Constr 0 [r_cred] =>
        match IsData.fromData r_cred with
        | some cred => some (.DCertDelegRegKey cred)
        | none => none
  | Data.Constr 1 [r_cred] =>
        match IsData.fromData r_cred with
        | some cred => some (.DCertDelegDeRegKey cred)
        | none => none
  | Data.Constr 2 [r_cred, r_pk] =>
      match IsData.fromData r_cred, IsData.fromData r_pk with
      | some cred, some pk => some (.DCertDelegDelegate cred pk)
      | _, _ => none
  | Data.Constr 3 [r_pk1, r_pk2] =>
      match IsData.fromData r_pk1, IsData.fromData r_pk2 with
      | some pk1, some pk2 => some (.DCertPoolRegister pk1 pk2)
      | _, _ => none
  | Data.Constr 4 [r_pk, r_idx] =>
      match IsData.fromData r_pk, IsData.fromData r_idx with
      | some pk, some idx => some (.DCertPoolRetire pk idx)
      | _, _ => none
  | Data.Constr 5 [] => some .DCertGenesis
  | Data.Constr 6 [] => some .DCertMir
  | _ => none


/-! List of predicates -/

/-- Return `true` only when `cert` is the registration certificate -/
def isRegisterCertificate (cert : DCert) : Bool :=
  match cert with
  | .DCertDelegRegKey _ => true
  | _ => false

/-- Return `true` only when `cert` is the deregistration certificate -/
def isDeRegisterCertificate (cert : DCert) : Bool :=
  match cert with
  | .DCertDelegDeRegKey _ => true
  | _ => false

/-- Return `true` only when `cert` is the delegation certificate -/
def isDelegationCertficate (cert : DCert) : Bool :=
  match cert with
  | .DCertDelegDelegate .. => true
  | _ => false


end CardanoLedgerApi.V1.DCert

