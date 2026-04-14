import CardanoLedgerApi.IsData.Class
import CardanoLedgerApi.V2
import PlutusCore

namespace CardanoLedgerApi.V3.TxCert

open IsData.Class
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)

abbrev ColdCommitteeCredential := V2.Credential
abbrev HotCommitteeCredential := V2.Credential
abbrev DRepCredential := V2.Credential


def ltOption [LT α] [DecidableLT α] (x y : Option α) : Bool :=
  match x, y with
  | .none, .some _ => true
  | .some a, .some b => a < b
  | _, _ => false

/-! DecidableLT instance for Option -/
theorem ltOption_true_imp_lt [LT α] [DecidableLT α] (x y : Option α) : ltOption x y → x < y := by
  cases x <;> cases y <;> simp [ltOption, LT.lt, Option.lt]

theorem ltOption_false_imp_not_lt [LT α] [DecidableLT α] (x y : Option α) : ltOption x y = false → ¬ x < y := by
  cases x <;> cases y <;> simp [ltOption, LT.lt, Option.lt]

def decLtOption [LT α] [DecidableLT α] (x y : Option α) : Decidable (LT.lt x y) :=
  match h:(ltOption x y) with
  | true => isTrue (ltOption_true_imp_lt _ _ h)
  | false => isFalse (ltOption_false_imp_not_lt _ _ h)

instance [LT α] [DecidableLT α] : DecidableLT (Option α) := decLtOption

/-- LE instance for Option -/
instance [LT α] : LE (Option α) where
  le x y := ¬ (y < x)

def leqOption [LT α] [DecidableLT α] (x y : Option α) : Bool := !(y < x)

/-! DecidableLE instance for Option -/
theorem leqOption_true_imp_le [LT α] [DecidableLT α] (x y : Option α) : leqOption x y → x ≤ y := by
  cases x <;> cases y <;> simp [leqOption, LE.le]

theorem leqOption_false_imp_not_le [LT α] [DecidableLT α] (x y : Option α) : leqOption x y = false → ¬ x ≤ y := by
  cases x <;> cases y <;> simp [leqOption, LE.le]

def decLeqOption [LT α] [DecidableLT α] (x y : Option α) : Decidable (LE.le x y) :=
  match h:(leqOption x y) with
  | true => isTrue (leqOption_true_imp_le _ _ h)
  | false => isFalse (leqOption_false_imp_not_le _ _ h)

instance [LT α] [DecidableLT α] : DecidableLE (Option α) := decLeqOption

/-! Std.Irrefl instance for Option -/
@[simp] theorem ltOptionD_same_false [LT α] [DecidableLT α] [Std.Irrefl (. < . : α → α → Prop)] (x : Option α) :
  ltOption x x = false := by cases x <;> simp [ltOption, Std.Irrefl.irrefl]

theorem Option_lt_irrefl [LT α] [DecidableLT α] [Std.Irrefl (. < . : α → α → Prop)] (x : Option α) : ¬ x < x :=
  by cases x <;> simp [Std.Irrefl.irrefl]

instance [LT α] [DecidableLT α] [Std.Irrefl (. < . : α → α → Prop)] : Std.Irrefl (. < . : (Option α) → (Option α) → Prop) where
  irrefl := Option_lt_irrefl


inductive DRep where
  | DRep : DRepCredential → DRep
  | DRepAlwaysAbstain : DRep
  | DRepAlwaysNoConfidence : DRep
deriving Repr

def beqDRep (x y : DRep) : Bool :=
  match x, y with
  | .DRep cred1, .DRep cred2 => cred1 == cred2
  | .DRepAlwaysAbstain, .DRepAlwaysAbstain
  | .DRepAlwaysNoConfidence, .DRepAlwaysNoConfidence => true
  | _, _ => false

/-- BEq instance for DRep -/
instance : BEq DRep := ⟨beqDRep⟩

/-! DecidableEq instance for DRep -/
@[simp] theorem beqDRep_iff_eq (x y : DRep) : beqDRep x y ↔ x = y := by
  cases x <;> cases y <;> simp [beqDRep]

@[simp] theorem beqDRep_false_iff_not_eq (x y : DRep) : beqDRep x y = false ↔ x ≠ y := by
  cases x <;> cases y <;> simp [beqDRep]

def decEqDRep (x y : DRep) : Decidable (Eq x y) :=
  match h:(beqDRep x y) with
  | true => isTrue ((beqDRep_iff_eq _ _).1 h)
  | false => isFalse ((beqDRep_false_iff_not_eq _ _).1 h)

instance : DecidableEq DRep := decEqDRep

/-! LawfulBEq instance for DRep -/
theorem beqDRep_reflexive (x : DRep) : beqDRep x x = true := by
   cases x <;> simp [beqDRep]

instance : LawfulBEq DRep where
  eq_of_beq {a b} := (beqDRep_iff_eq a b).1
  rfl {bs} := by simp [BEq.beq]


def ltDRep (x y : DRep) : Bool :=
  match x, y with
  | .DRep cred1, .DRep cred2 => cred1 < cred2
  | .DRep _, _ => true
  | .DRepAlwaysAbstain, .DRepAlwaysNoConfidence => true
  | .DRepAlwaysAbstain, _
  | .DRepAlwaysNoConfidence, _ => false

/-- LT instance for DRep -/
instance : LT DRep where
  lt x y := ltDRep x y

/-! DecidableLT instance for DRep -/
theorem ltDRep_true_imp_lt (x y : DRep) : ltDRep x y → x < y := by
  cases x <;> cases y <;> simp only [ltDRep, LT.lt] <;> simp

theorem ltDRep_false_imp_not_lt (x y : DRep) :
  ltDRep x y = false → ¬ x < y := by
    cases x <;> cases y <;> simp only [ltDRep, LT.lt] <;> simp

def decLtDRep (x y : DRep) : Decidable (LT.lt x y) :=
  match h:(ltDRep x y) with
  | true => isTrue (ltDRep_true_imp_lt _ _ h)
  | false => isFalse (ltDRep_false_imp_not_lt _ _ h)

instance : DecidableLT DRep := decLtDRep

/-! Std.Irrefl instance for DRep -/
@[simp] theorem ltDRep_same_false (x : DRep) : ltDRep x x = false := by cases x <;> simp [ltDRep, LT.lt]

theorem DRep_lt_irrefl (x : DRep) : ¬ x < x := by cases x <;> simp [LT.lt]

instance : Std.Irrefl (. < . : DRep → DRep → Prop) where
  irrefl := DRep_lt_irrefl

/-- LE instance for DRep -/
instance : LE DRep where
  le x y := ¬ (y < x)

/-! DecidableLE instance for DRep -/
instance : DecidableLE DRep :=
  fun x y => inferInstanceAs (Decidable (¬ (y < x)))

/-- IsData instance for DRep -/
instance : IsData DRep where
  toData
  | .DRep cred => mkDataConstr 0 [IsData.toData cred]
  | .DRepAlwaysAbstain => mkDataConstr 1
  | .DRepAlwaysNoConfidence => mkDataConstr 2
  fromData
  | Data.Constr 0 [r_cred] =>
        match IsData.fromData r_cred with
        | some cred => some (.DRep cred)
        | none => none
  | Data.Constr 1 [] => some .DRepAlwaysAbstain
  | Data.Constr 2 [] => some .DRepAlwaysNoConfidence
  | _ => none


inductive Delegatee where
  | DelegStake : V2.PubKeyHash → Delegatee
  | DelegVote : DRep → Delegatee
  | DelegStakeVote : V2.PubKeyHash → DRep → Delegatee
deriving Repr


def beqDelegatee (x y : Delegatee) : Bool :=
  match x, y with
  | .DelegStake pk1, .DelegStake pk2 => pk1 == pk2
  | .DelegVote d1, .DelegVote d2 => d1 == d2
  | .DelegStakeVote pk1 d1, .DelegStakeVote pk2 d2 => pk1 == pk2 && d1 == d2
  | _, _ => false

/-- BEq instance for Delegatee -/
instance : BEq Delegatee := ⟨beqDelegatee⟩

/-! DecidableEq instance for Delegatee -/
@[simp] theorem beqDelegatee_iff_eq (x y : Delegatee) : beqDelegatee x y ↔ x = y := by
  cases x <;> cases y <;> simp [beqDelegatee]

@[simp] theorem beqDelegatee_false_iff_not_eq (x y : Delegatee) : beqDelegatee x y = false ↔ x ≠ y := by
  cases x <;> cases y <;> simp [beqDelegatee]

def Delegatee.decEq (x y : Delegatee) : Decidable (Eq x y) :=
  match h:(beqDelegatee x y) with
  | true => isTrue ((beqDelegatee_iff_eq _ _).1 h)
  | false => isFalse ((beqDelegatee_false_iff_not_eq _ _).1 h)

instance : DecidableEq Delegatee := Delegatee.decEq

/-! LawfulBEq instance for Delegatee -/
theorem beqDelegatee_reflexive (x : Delegatee) : beqDelegatee x x = true := by
   cases x <;> simp [beqDelegatee]

instance : LawfulBEq Delegatee where
  eq_of_beq {a b} := (beqDelegatee_iff_eq a b).1
  rfl {bs} := by simp [BEq.beq]


def ltDelegatee (x y : Delegatee) : Bool :=
  match x, y with
  | .DelegStake pk1, .DelegStake pk2 => pk1 < pk2
  | .DelegStake _, _ => true
  | .DelegVote d1, .DelegVote d2 => d1 < d2
  | .DelegVote _, .DelegStakeVote .. => true
  | .DelegVote _, _ => false
  | .DelegStakeVote pk1 d1, .DelegStakeVote pk2 d2 => pk1 < pk2 || (pk1 == pk2 && d1 < d2)
  | .DelegStakeVote .., _ => false

/-- LT instance for Delegatee -/
instance : LT Delegatee where
  lt x y := ltDelegatee x y

/-! DecidableLT instance for Delegatee -/
theorem ltDelegatee_true_imp_lt (x y : Delegatee) : ltDelegatee x y → x < y := by
  cases x <;> cases y <;> simp only [ltDelegatee, LT.lt] <;> simp

theorem ltDelegatee_false_imp_not_lt (x y : Delegatee) :
  ltDelegatee x y = false → ¬ x < y := by
    cases x <;> cases y <;> simp only [ltDelegatee, LT.lt] <;> simp

def decLtDelegatee (x y : Delegatee) : Decidable (LT.lt x y) :=
  match h:(ltDelegatee x y) with
  | true => isTrue (ltDelegatee_true_imp_lt _ _ h)
  | false => isFalse (ltDelegatee_false_imp_not_lt _ _ h)

instance : DecidableLT Delegatee := decLtDelegatee

/-! Std.Irrefl instance for Delegatee -/
@[simp] theorem ltDelegatee_same_false (x : Delegatee) : ltDelegatee x x = false := by
  cases x <;> simp only [ltDelegatee, LT.lt] <;> simp <;> repeat' apply String.le_refl

theorem Delegatee_lt_irrefl (x : Delegatee) : ¬ x < x := by cases x <;> simp [LT.lt]

instance : Std.Irrefl (. < . : Delegatee → Delegatee → Prop) where
  irrefl := Delegatee_lt_irrefl

/-- LE instance for Delegatee -/
instance : LE Delegatee where
  le x y := ¬ (y < x)

/-! DecidableLE instance for Delegatee -/
instance : DecidableLE Delegatee :=
  fun x y => inferInstanceAs (Decidable (¬ (y < x)))

/-- IsData instance for Delegatee -/
instance : IsData Delegatee where
  toData
  | .DelegStake pk => mkDataConstr 0 [IsData.toData pk]
  | .DelegVote d => mkDataConstr 1 [IsData.toData d]
  | .DelegStakeVote pk d => mkDataConstr 2 [IsData.toData pk, IsData.toData d]
  fromData
  | Data.Constr 0 [r_pk] =>
        match IsData.fromData r_pk with
        | some pk => some (.DelegStake pk)
        | none => none
  | Data.Constr 1 [r_d] =>
        match IsData.fromData r_d with
        | some d => some (.DelegVote d)
        | none => none
  | Data.Constr 2 [r_pk, r_d] =>
        match IsData.fromData r_pk, IsData.fromData r_d with
        | some pk, some d => some (.DelegStakeVote pk d)
        | _, _ => none
  | _ => none


/-- A representation of the ledger TxCert. -/
inductive TxCert where
    /-- Register staking credential with an optional deposit amount -/
  | TxCertRegStaking : V2.Credential → Option Integer → TxCert
    /-- Un-Register staking credential with an optional refund amount -/
  | TxCertUnRegStaking : V2.Credential → Option Integer → TxCert
    /-- Delegate staking credential to a Delegatee -/
  | TxCertDelegStaking : V2.Credential → Delegatee → TxCert
    /-- Register and delegate staking credential to a Delegatee in one certificate. Note that deposit is mandatory. -/
  | TxCertRegDeleg : V2.Credential → Delegatee → Integer → TxCert
    /-- Register a DRep with a deposit value. The optional anchor is omitted. -/
  | TxCertRegDRep : DRepCredential → Integer → TxCert
    /-- Update a DRep. The optional anchor is omitted. -/
  | TxCertUpdateDRep : DRepCredential → TxCert
    /-- UnRegister a DRep with mandatory refund value -/
  | TxCertUnRegDRep : DRepCredential → Integer → TxCert
    /-- A digest of the PoolParams -/
  | TxCertPoolRegister : V2.PubKeyHash → V2.PubKeyHash → TxCert
    /-- The retirement certificate and the Epoch in which the retirement will take place. -/
  | TxCertPoolRetire : V2.PubKeyHash → Integer → TxCert
    /-- Authorize a Hot credential for a specific Committee member's cold credential -/
  | TxCertAuthHotCommittee : ColdCommitteeCredential → HotCommitteeCredential → TxCert
  | TxCertResignColdCommittee : ColdCommitteeCredential → TxCert
deriving Repr

def beqTxCert (x y : TxCert) : Bool :=
  match x, y with
  | .TxCertRegStaking cred1 n1, .TxCertRegStaking cred2 n2
  | .TxCertUnRegStaking cred1 n1, .TxCertUnRegStaking cred2 n2 => cred1 == cred2 && n1 == n2
  | .TxCertDelegStaking cred1 d1, .TxCertDelegStaking cred2 d2 => cred1 == cred2 && d1 == d2
  | .TxCertRegDeleg cred1 d1 n1, .TxCertRegDeleg cred2 d2 n2 => cred1 == cred2 && d1 == d2 && n1 == n2
  | .TxCertRegDRep cred1 n1, .TxCertRegDRep cred2 n2 => cred1 == cred2 && n1 == n2
  | .TxCertUpdateDRep cred1, .TxCertUpdateDRep cred2 => cred1 == cred2
  | .TxCertUnRegDRep cred1 n1, .TxCertUnRegDRep cred2 n2 => cred1 == cred2 && n1 == n2
  | .TxCertPoolRegister pk1 pk2, .TxCertPoolRegister pk1' pk2' => pk1 == pk1' && pk2 == pk2'
  | .TxCertPoolRetire pk1 n1, .TxCertPoolRetire pk2 n2 => pk1 == pk2 && n1 == n2
  | .TxCertAuthHotCommittee c1 h1, .TxCertAuthHotCommittee c2 h2 => c1 == c2 && h1 == h2
  | .TxCertResignColdCommittee c1, .TxCertResignColdCommittee c2 => c1 == c2
  | _, _ => false

/-- BEq instance for TxCert -/
instance : BEq TxCert := ⟨beqTxCert⟩

/-! DecidableEq instance for TxCert -/
@[simp] theorem beqTxCert_iff_eq (x y : TxCert) : beqTxCert x y ↔ x = y := by
  cases x <;> cases y <;> simp [beqTxCert]
  apply Iff.intro <;>
    . repeat' rw [and_imp];
      intros; repeat' constructor <;> repeat' assumption

@[simp] theorem beqTxCert_false_iff_not_eq (x y : TxCert) : beqTxCert x y = false ↔ x ≠ y := by
  cases x <;> cases y <;> simp [beqTxCert]

def TxCert.decEq (x y : TxCert) : Decidable (Eq x y) :=
  match h:(beqTxCert x y) with
  | true => isTrue ((beqTxCert_iff_eq _ _).1 h)
  | false => isFalse ((beqTxCert_false_iff_not_eq _ _).1 h)

instance : DecidableEq TxCert := TxCert.decEq

/-! LawfulBEq instance for TxCert -/
theorem beqTxCert_reflexive (x : TxCert) : beqTxCert x x = true := by
   cases x <;> simp [beqTxCert]

instance : LawfulBEq TxCert where
  eq_of_beq {a b} := (beqTxCert_iff_eq a b).1
  rfl {bs} := by simp [BEq.beq]


def ltTxCert (x y : TxCert) : Bool :=
  match x, y with
  | .TxCertRegStaking cred1 n1, .TxCertRegStaking cred2 n2 => cred1 < cred2 || (cred1 == cred2 && n1 < n2)
  | .TxCertRegStaking .., _ => true
  | .TxCertUnRegStaking cred1 n1, .TxCertUnRegStaking cred2 n2 => cred1 < cred2 || (cred1 == cred2 && n1 < n2)
  | .TxCertUnRegStaking ..,  .TxCertRegStaking .. => false
  | .TxCertUnRegStaking .., _ => true
  | .TxCertDelegStaking cred1 d1, .TxCertDelegStaking cred2 d2 => cred1 < cred2 || (cred1 == cred2 && d1 < d2)
  | .TxCertDelegStaking .., .TxCertRegStaking ..
  | .TxCertDelegStaking .., .TxCertUnRegStaking .. => false
  | .TxCertDelegStaking .., _ => true
  | .TxCertRegDeleg cred1 d1 n1, .TxCertRegDeleg cred2 d2 n2 =>
         cred1 < cred2 || (cred1 == cred2 && (d1 < d2 || (d1 == d2 && n1 < n2)))
  | .TxCertRegDeleg .., .TxCertRegStaking ..
  | .TxCertRegDeleg .., .TxCertUnRegStaking ..
  | .TxCertRegDeleg .., .TxCertDelegStaking .. => false
  | .TxCertRegDeleg .., _ => true
  | .TxCertRegDRep cred1 n1, .TxCertRegDRep cred2 n2 => cred1 < cred2 || (cred1 == cred2 && n1 < n2)
  | .TxCertRegDRep .., .TxCertRegStaking ..
  | .TxCertRegDRep .., .TxCertUnRegStaking ..
  | .TxCertRegDRep .., .TxCertDelegStaking ..
  | .TxCertRegDRep .., .TxCertRegDeleg .. => false
  | .TxCertRegDRep .., _ => true
  | .TxCertUpdateDRep cred1, .TxCertUpdateDRep cred2 => cred1 < cred2
  | .TxCertUpdateDRep _, .TxCertRegStaking ..
  | .TxCertUpdateDRep _, .TxCertUnRegStaking ..
  | .TxCertUpdateDRep _, .TxCertDelegStaking ..
  | .TxCertUpdateDRep _, .TxCertRegDeleg ..
  | .TxCertUpdateDRep _, .TxCertRegDRep .. => false
  | .TxCertUpdateDRep _, _ => true
  | .TxCertUnRegDRep cred1 n1, .TxCertUnRegDRep cred2 n2 => cred1 < cred2 || (cred1 == cred2 && n1 < n2)
  | .TxCertUnRegDRep .., .TxCertRegStaking ..
  | .TxCertUnRegDRep .., .TxCertUnRegStaking ..
  | .TxCertUnRegDRep .., .TxCertDelegStaking ..
  | .TxCertUnRegDRep .., .TxCertRegDeleg ..
  | .TxCertUnRegDRep .., .TxCertRegDRep ..
  | .TxCertUnRegDRep .., .TxCertUpdateDRep _ => false
  | .TxCertUnRegDRep .., _ => true
  | .TxCertPoolRegister pk1 pk2, .TxCertPoolRegister pk1' pk2' => pk1 < pk1' || (pk1 == pk1' && pk2 < pk2')
  | .TxCertPoolRegister .., .TxCertRegStaking ..
  | .TxCertPoolRegister .., .TxCertUnRegStaking ..
  | .TxCertPoolRegister .., .TxCertDelegStaking ..
  | .TxCertPoolRegister .., .TxCertRegDeleg ..
  | .TxCertPoolRegister .., .TxCertRegDRep ..
  | .TxCertPoolRegister .., .TxCertUpdateDRep _
  | .TxCertPoolRegister .., .TxCertUnRegDRep .. => false
  | .TxCertPoolRegister .., _ => true
  | .TxCertPoolRetire pk1 n1, .TxCertPoolRetire pk2 n2 => pk1 < pk2 || (pk1 == pk2 && n1 < n2)
  | .TxCertPoolRetire .., .TxCertRegStaking ..
  | .TxCertPoolRetire .., .TxCertUnRegStaking ..
  | .TxCertPoolRetire .., .TxCertDelegStaking ..
  | .TxCertPoolRetire .., .TxCertRegDeleg ..
  | .TxCertPoolRetire .., .TxCertRegDRep ..
  | .TxCertPoolRetire .., .TxCertUpdateDRep _
  | .TxCertPoolRetire .., .TxCertUnRegDRep ..
  | .TxCertPoolRetire .., .TxCertPoolRegister .. => false
  | .TxCertPoolRetire .., _ => true
  | .TxCertAuthHotCommittee c1 h1, .TxCertAuthHotCommittee c2 h2 => c1 < c2 || (c1 == c2 && h1 < h2)
  | .TxCertAuthHotCommittee .., .TxCertResignColdCommittee .. => true
  | .TxCertAuthHotCommittee .., _ => false
  | .TxCertResignColdCommittee c1, .TxCertResignColdCommittee c2 => c1 < c2
  | .TxCertResignColdCommittee _, _ => false

/-- LT instance for TxCert -/
instance : LT TxCert where
  lt x y := ltTxCert x y

/-! DecidableLT instance for TxCert -/
theorem ltTxCert_true_imp_lt (x y : TxCert) : ltTxCert x y → x < y := by
  cases x <;> cases y <;> simp only [ltTxCert, LT.lt] <;> simp

theorem ltTxCert_false_imp_not_lt (x y : TxCert) :
  ltTxCert x y = false → ¬ x < y := by
    cases x <;> cases y <;> simp only [ltTxCert, LT.lt] <;> simp

def TxCert.decLt (x y : TxCert) : Decidable (LT.lt x y) :=
  match h:(ltTxCert x y) with
  | true => isTrue (ltTxCert_true_imp_lt _ _ h)
  | false => isFalse (ltTxCert_false_imp_not_lt _ _ h)

instance : DecidableLT TxCert := TxCert.decLt

/-! Std.Irrefl instance for TxCert -/
@[simp] theorem ltTxCert_same_false (x : TxCert) : ltTxCert x x = false := by
    cases x <;> simp only [ltTxCert] <;> simp <;> try constructor <;> simp [LT.lt]
    repeat' apply Option_lt_irrefl
    repeat' apply V1.Credential.Credential.lt_irrefl

theorem TxCert.lt_irrefl (x : TxCert) : ¬ x < x := by cases x <;> simp [LT.lt]

instance : Std.Irrefl (. < . : TxCert → TxCert → Prop) where
  irrefl := TxCert.lt_irrefl

/-- LE instance for TxCert -/
instance : LE TxCert where
  le x y := ¬ (y < x)

/-! DecidableLE instance for TxCert -/
instance : DecidableLE TxCert :=
  fun x y => inferInstanceAs (Decidable (¬ (y < x)))


/-- IsData instance for TxCert -/
instance : IsData TxCert where
  toData
  | .TxCertRegStaking cred n => mkDataConstr 0 [IsData.toData cred, IsData.toData n]
  | .TxCertUnRegStaking cred n => mkDataConstr 1 [IsData.toData cred, IsData.toData n]
  | .TxCertDelegStaking cred d => mkDataConstr 2 [IsData.toData cred, IsData.toData d]
  | .TxCertRegDeleg cred d n => mkDataConstr 3 [IsData.toData cred, IsData.toData d, IsData.toData n]
  | .TxCertRegDRep cred n => mkDataConstr 4 [IsData.toData cred, IsData.toData n]
  | .TxCertUpdateDRep cred => mkDataConstr 5 [IsData.toData cred]
  | .TxCertUnRegDRep cred n => mkDataConstr 6 [IsData.toData cred, IsData.toData n]
  | .TxCertPoolRegister pk1 pk2 => mkDataConstr 7 [IsData.toData pk1, IsData.toData pk2]
  | .TxCertPoolRetire pk n => mkDataConstr 8 [IsData.toData pk, IsData.toData n]
  | .TxCertAuthHotCommittee c h => mkDataConstr 9 [IsData.toData c, IsData.toData h]
  | .TxCertResignColdCommittee c => mkDataConstr 10 [IsData.toData c]
  fromData
  | Data.Constr 0 [r_cred, r_n] =>
        match IsData.fromData r_cred, IsData.fromData r_n with
        | some cred, some n => some (.TxCertRegStaking cred n)
        | _, _ => none
  | Data.Constr 1 [r_cred, r_n] =>
        match IsData.fromData r_cred, IsData.fromData r_n with
        | some cred, some n => some (.TxCertUnRegStaking cred n)
        | _, _ => none
  | Data.Constr 2 [r_cred, r_d] =>
      match IsData.fromData r_cred, IsData.fromData r_d with
      | some cred, some d => some (.TxCertDelegStaking cred d)
      | _, _ => none
  | Data.Constr 3 [r_cred, r_d, r_n] =>
      match IsData.fromData r_cred, IsData.fromData r_d, IsData.fromData r_n  with
      | some cred, some d, some n => some (.TxCertRegDeleg cred d n)
      | _, _, _ => none
  | Data.Constr 4 [r_cred, r_n] =>
      match IsData.fromData r_cred, IsData.fromData r_n with
      | some cred, some n => some (.TxCertRegDRep cred n)
      | _, _ => none
  | Data.Constr 5 [r_cred] =>
      match IsData.fromData r_cred with
      | some cred => some (.TxCertUpdateDRep cred)
      | none => none
  | Data.Constr 6 [r_cred, r_n] =>
      match IsData.fromData r_cred, IsData.fromData r_n with
      | some cred, some n => some (.TxCertUnRegDRep cred n)
      | _, _ => none
  | Data.Constr 7 [r_pk1, r_pk2] =>
      match IsData.fromData r_pk1, IsData.fromData r_pk2 with
      | some pk1, some pk2 => some (.TxCertPoolRegister pk1 pk2)
      | _, _ => none
  | Data.Constr 8 [r_pk, r_n] =>
      match IsData.fromData r_pk, IsData.fromData r_n with
      | some pk, some n => some (.TxCertPoolRetire pk n)
      | _, _ => none
  | Data.Constr 9 [r_c, r_h] =>
      match IsData.fromData r_c, IsData.fromData r_h with
      | some c, some h => some (.TxCertAuthHotCommittee c h)
      | _, _ => none
  | Data.Constr 10 [r_c] =>
      match IsData.fromData r_c with
      | some c => some (.TxCertResignColdCommittee c)
      | none => none
  | _ => none


/-! List of predicates -/

/-- Return `true` only when `cert` is the registration staking credential certificate -/
def isRegisterStakingCertificate (cert : TxCert) : Bool :=
  match cert with
  | .TxCertRegStaking .. => true
  | _ => false

/-- Return `true` only when `cert` is the un-registration staking credential certificate -/
def isUnRegisterStakingCertificate (cert : TxCert) : Bool :=
  match cert with
  | .TxCertUnRegStaking .. => true
  | _ => false

/-- Return `true` only when `cert` is the delegation staking credential certificate -/
def isDelegationStakingCertficate (cert : TxCert) : Bool :=
  match cert with
  | .TxCertDelegStaking .. => true
  | _ => false

/-- Return `true` only when `cert` is the resigration and delegation staking credential certificate -/
def isRegisterAndDelegationCertficate (cert : TxCert) : Bool :=
  match cert with
  | .TxCertRegDeleg .. => true
  | _ => false


end CardanoLedgerApi.V3.TxCert

