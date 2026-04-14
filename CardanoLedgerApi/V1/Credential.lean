import CardanoLedgerApi.IsData.Class
import CardanoLedgerApi.V1.Scripts
import PlutusCore

namespace CardanoLedgerApi.V1.Credential
open IsData.Class
open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)
open Scripts

/-- `PubKeyHash` is an alias to `ByteString` -/
abbrev PubKeyHash := ByteString

/-- IsData instance for PubKeyHash -/
instance : IsData PubKeyHash where
  toData := Data.B
  fromData
  | Data.B pk => some pk
  | _ => none

/--  Credentials required to unlock a transaction output. -/
inductive Credential where
  | PubKeyCredential : PubKeyHash → Credential
  | ScriptCredential : ScriptHash → Credential
deriving Repr


def beqCredential (x y : Credential) : Bool :=
  match x, y with
  | .PubKeyCredential phk1, .PubKeyCredential phk2 => phk1 == phk2
  | .ScriptCredential shk1, .ScriptCredential shk2 => shk1 == shk2
  | _, _=> false

/-- BEq instance for Credential -/
instance : BEq Credential := ⟨beqCredential⟩

/-! DecidableEq instance for Credential -/
@[simp] theorem beqCredential_iff_eq (x y : Credential) : beqCredential x y ↔ x = y := by
  cases x <;> cases y <;> simp [beqCredential]

@[simp] theorem beqCredential_false_iff_not_eq (x y : Credential) : beqCredential x y = false ↔ x ≠ y := by
  cases x <;> cases y <;> simp [beqCredential]

def Credential.decEq (x y : Credential) : Decidable (Eq x y) :=
  match h:(beqCredential x y) with
  | true => isTrue ((beqCredential_iff_eq _ _).1 h)
  | false => isFalse ((beqCredential_false_iff_not_eq _ _).1 h)

instance : DecidableEq Credential := Credential.decEq

/-! LawfulBEq instance for Credential -/
theorem beqCredential_reflexive (x : Credential) : beqCredential x x = true := by
   cases x <;> simp [beqCredential]

instance : LawfulBEq Credential where
  eq_of_beq {a b} := (beqCredential_iff_eq a b).1
  rfl {bs} := by simp [BEq.beq]


def ltCredential (x y : Credential) : Bool :=
  match x, y with
  | .PubKeyCredential pk1, .PubKeyCredential pk2 => pk1 < pk2
  | .ScriptCredential sh1, .ScriptCredential sh2 => sh1 < sh2
  | .PubKeyCredential _, .ScriptCredential _ => true
  | .ScriptCredential _, .PubKeyCredential _ => false

/-- LT instance for Credential -/
instance : LT Credential where
  lt x y := ltCredential x y

/-! DecidableLT instance for Credential -/
theorem ltCredential_true_imp_lt (x y : Credential) : ltCredential x y → x < y := by
  cases x <;> cases y <;> simp only [ltCredential, LT.lt] <;> simp

theorem ltCredential_false_imp_not_lt (x y : Credential) :
  ltCredential x y = false → ¬ x < y := by
    cases x <;> cases y <;> simp only [ltCredential, LT.lt] <;> simp

def Credential.decLt (x y : Credential) : Decidable (LT.lt x y) :=
  match h:(ltCredential x y) with
  | true => isTrue (ltCredential_true_imp_lt _ _ h)
  | false => isFalse (ltCredential_false_imp_not_lt _ _ h)

instance : DecidableLT Credential := Credential.decLt

/-! Std.Irrefl instance for Credential -/
@[simp] theorem ltCredential_same_false (x : Credential) : ltCredential x x = false := by
    cases x <;> simp only [ltCredential, LT.lt] <;> simp <;> apply String.lt_irrefl

theorem Credential.lt_irrefl (x : Credential) : ¬ x < x := by cases x <;> simp [LT.lt]

instance : Std.Irrefl (. < . : Credential → Credential → Prop) where
  irrefl := Credential.lt_irrefl

/-- LE instance for Credential -/
instance : LE Credential where
  le x y := ¬ (y < x)

/-! DecidableLE instance for Credential -/
instance : DecidableLE Credential :=
  fun x y => inferInstanceAs (Decidable (¬ (y < x)))

/-- IsData instance for Credential -/
instance : IsData Credential where
  toData
  | .PubKeyCredential pk => mkDataConstr 0 [Data.B pk]
  | .ScriptCredential sh => mkDataConstr 1 [Data.B sh]
  fromData
  | Data.Constr 0 [Data.B pk] => some (.PubKeyCredential pk)
  | Data.Constr 1 [Data.B sh] => some (.ScriptCredential sh)
  | _ => none

/--  Staking credential used to assign rewards. -/
inductive StakingCredential where
  | StakingHash : Credential → StakingCredential
  | StakingPtr : Integer → Integer → Integer → StakingCredential
deriving Repr

def beqStakingCredential (x y : StakingCredential) : Bool :=
  match x, y with
  | .StakingHash h1, .StakingHash h2 => h1 == h2
  | .StakingPtr n1 n2 n3, .StakingPtr m1 m2 m3 => n1 == m1 && n2 == m2 && n3 == m3
  | _, _ => false

/-- BEq instance for StakingCredential -/
instance : BEq StakingCredential := ⟨beqStakingCredential⟩

/-! DecidableEq instance for StakingCredential -/
theorem beqStakingCredential_iff_eq (x y : StakingCredential) : beqStakingCredential x y ↔ x = y := by
  cases x <;> cases y <;>
  apply Iff.intro <;> simp [beqStakingCredential] <;>
  intro h1 h2 h3 <;> repeat' constructor <;> repeat' assumption

theorem beqStakingCredential_false_iff_not_eq (x y : StakingCredential) : beqStakingCredential x y = false ↔ x ≠ y := by
  cases x <;> cases y <;> simp [beqStakingCredential]

def StakingCredential.decEq (x y : StakingCredential) : Decidable (Eq x y) :=
  match h:(beqStakingCredential x y) with
  | true => isTrue ((beqStakingCredential_iff_eq _ _).1 h)
  | false => isFalse ((beqStakingCredential_false_iff_not_eq _ _).1 h)

instance : DecidableEq StakingCredential := StakingCredential.decEq

/-! LawfulBEq instance for StakingCredential -/
theorem beqStakingCredential_reflexive (x : StakingCredential) : beqStakingCredential x x = true := by
  cases x <;> simp [beqStakingCredential]

instance : LawfulBEq StakingCredential where
  eq_of_beq {a b} := (beqStakingCredential_iff_eq a b).1
  rfl {bs} := by simp [BEq.beq]; apply beqStakingCredential_reflexive


def ltStakingCredential (x y : StakingCredential) : Bool :=
  match x, y with
  | .StakingHash cred1, .StakingHash cred2 => cred1 < cred2
  | .StakingHash _, .StakingPtr .. => true
  | .StakingPtr n1 n2 n3, .StakingPtr m1 m2 m3 =>
     n1 < m1 || (n1 == m1 && n2 < m2) ||
     (n1 == m1 && n2 == m2 && n3 < m3)
  | .StakingPtr .., .StakingHash _ => false

/-- LT instance for StakingCredential -/
instance : LT StakingCredential where
  lt x y := ltStakingCredential x y

/-! DecidableLT instance for StakingCredential -/
theorem ltStakingCredential_true_imp_lt (x y : StakingCredential) : ltStakingCredential x y → x < y := by
  cases x <;> cases y <;> simp only [ltStakingCredential, LT.lt] <;> simp

theorem ltStakingCredential_false_imp_not_lt (x y : StakingCredential) :
  ltStakingCredential x y = false → ¬ x < y := by
    cases x <;> cases y <;> simp only [ltStakingCredential, LT.lt] <;> simp

def StakingCredential.decLt (x y : StakingCredential) : Decidable (LT.lt x y) :=
  match h:(ltStakingCredential x y) with
  | true => isTrue (ltStakingCredential_true_imp_lt _ _ h)
  | false => isFalse (ltStakingCredential_false_imp_not_lt _ _ h)

instance : DecidableLT StakingCredential := StakingCredential.decLt

@[simp] theorem ltStakingCredential_same_false (x : StakingCredential) : ltStakingCredential x x = false := by
  cases x <;> simp [ltStakingCredential] <;> apply Credential.lt_irrefl

/-! Std.Irrefl instance for StakingCredential -/
theorem StakingCredential.lt_irrefl (x : StakingCredential) : ¬ x < x := by cases x <;> simp [LT.lt]


instance : Std.Irrefl (. < . : StakingCredential → StakingCredential → Prop) where
  irrefl := StakingCredential.lt_irrefl

/-- LE instance for StakingCredential -/
instance : LE StakingCredential where
  le x y := ¬ (y < x)

/-! DecidableLE instance for StakingCredential -/
instance : DecidableLE StakingCredential :=
  fun x y => inferInstanceAs (Decidable (¬ (y < x)))

/-- IsData instance for StakingCredential -/
instance : IsData StakingCredential where
  toData
  | .StakingHash cred => mkDataConstr 0 [IsData.toData cred]
  | .StakingPtr n1 n2 n3 => mkDataConstr 1 [Data.I n1, Data.I n2, Data.I n3]
  fromData
  | Data.Constr 0 [r_cred] =>
       match IsData.fromData r_cred with
       | none => none
       | some cred => some (.StakingHash cred)
  | Data.Constr 1 [Data.I n1, Data.I n2, Data.I n3] => some (.StakingPtr n1 n2 n3)
  | _ => none


/-! List of predicates -/

/-- Return `true` only when cred is a script credential corresponding to `sh` -/
def hasScriptCredential (sh : ScriptHash) (cred : Credential) : Bool :=
  match cred with
  | .ScriptCredential sh' => sh' == sh
  | _ => false

/-- Return `true` only when cred is a public key credential corresponding to `pk` -/
def hasPubKeyCredential (pk : PubKeyHash) (cred : Credential) : Bool :=
  match cred with
  | .PubKeyCredential pk' => pk' == pk
  | _ => false


/-- Return `true` only when cred is a script credential. -/
def isScriptCredential (cred : Credential) : Bool :=
  match cred with
  | .ScriptCredential _ => true
  | _ => false

/-- Return `true` only when cred is a script credential. -/
def isPubKeyCredential (cred : Credential) : Bool :=
  match cred with
  | .PubKeyCredential _ => true
  | _ => false

/-- Return `true` only when cred is a staking script credential. -/
def isStakingScriptCredential (cred : StakingCredential) : Bool :=
  match cred with
  | .StakingHash (.ScriptCredential _) => true
  | _ => false


end CardanoLedgerApi.V1.Credential
