import CardanoLedgerApi.IsData.Class
import CardanoLedgerApi.V3.Tx
import CardanoLedgerApi.V3.TxCert
import PlutusCore

namespace CardanoLedgerApi.V3.Governance

namespace V3
  open Tx
  export Tx (
    TxId
    TxOutRef
  )
end V3

namespace V2
  open CardanoLedgerApi.V2
  export CardanoLedgerApi.V2 (
    PubKeyHash
  )
end V2

open IsData.Class
open TxCert (ColdCommitteeCredential DRepCredential HotCommitteeCredential)
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)

inductive Voter where
 | CommitteeVoter : HotCommitteeCredential → Voter
 | DRepVoter : DRepCredential → Voter
 | StakePoolVoter : V2.PubKeyHash → Voter
deriving Repr


def beqVoter (x y : Voter) : Bool :=
  match x, y with
  | .CommitteeVoter cred1, .CommitteeVoter cred2 => cred1 == cred2
  | .DRepVoter cred1, .DRepVoter cred2 => cred1 == cred2
  | .StakePoolVoter pk1, .StakePoolVoter pk2 => pk1 == pk2
  | _, _ => false

/-- BEq instance for Voter -/
instance : BEq Voter := ⟨beqVoter⟩

/-! DecidableEq instance for Voter -/
@[simp] theorem beqVoter_iff_eq (x y : Voter) : beqVoter x y ↔ x = y := by
  cases x <;> cases y <;> simp [beqVoter]

@[simp] theorem beqVoter_false_iff_not_eq (x y : Voter) : beqVoter x y = false ↔ x ≠ y := by
  cases x <;> cases y <;> simp [beqVoter]

def decEqVoter (x y : Voter) : Decidable (Eq x y) :=
  match h:(beqVoter x y) with
  | true => isTrue ((beqVoter_iff_eq _ _).1 h)
  | false => isFalse ((beqVoter_false_iff_not_eq _ _).1 h)

instance : DecidableEq Voter := decEqVoter

/-! LawfulBEq instance for Voter -/
theorem beqVoter_reflexive (x : Voter) : beqVoter x x = true := by
   cases x <;> simp [beqVoter]

instance : LawfulBEq Voter where
  eq_of_beq {a b} := (beqVoter_iff_eq a b).1
  rfl {bs} := by simp [BEq.beq]


def ltVoter (x y : Voter) : Bool :=
  match x, y with
  | .CommitteeVoter cred1, .CommitteeVoter cred2 => cred1 < cred2
  | .CommitteeVoter _, _ => true
  | .DRepVoter cred1, .DRepVoter cred2 => cred1 < cred2
  | .DRepVoter _, .CommitteeVoter _ => false
  | .DRepVoter _, _ => true
  | .StakePoolVoter pk1, .StakePoolVoter pk2 => pk1 < pk2
  | .StakePoolVoter _, _ => false

/-- LT instance for Voter -/
instance : LT Voter where
  lt x y := ltVoter x y

/-! DecidableLT instance for Voter -/
theorem ltVoter_true_imp_lt (x y : Voter) : ltVoter x y → x < y := by
  cases x <;> cases y <;> simp only [ltVoter, LT.lt] <;> simp

theorem ltVoter_false_imp_not_lt (x y : Voter) :
  ltVoter x y = false → ¬ x < y := by
    cases x <;> cases y <;> simp only [ltVoter, LT.lt] <;> simp

def decLtVoter (x y : Voter) : Decidable (LT.lt x y) :=
  match h:(ltVoter x y) with
  | true => isTrue (ltVoter_true_imp_lt _ _ h)
  | false => isFalse (ltVoter_false_imp_not_lt _ _ h)

instance : DecidableLT Voter := decLtVoter

/-! Std.Irrefl instance for Voter -/
@[simp] theorem ltVoter_same_false (x : Voter) : ltVoter x x = false := by
  cases x <;> simp only [ltVoter, LT.lt] <;> simp; apply String.lt_irrefl

theorem Voter_lt_irrefl (x : Voter) : ¬ x < x := by cases x <;> simp [LT.lt]

instance : Std.Irrefl (. < . : Voter → Voter → Prop) where
  irrefl := Voter_lt_irrefl

/-- LE instance for Voter -/
instance : LE Voter where
  le x y := ¬ (y < x)

/-! DecidableLE instance for Voter -/
instance : DecidableLE Voter :=
  fun x y => inferInstanceAs (Decidable (¬ (y < x)))

/-- IsData instance for Voter -/
instance : IsData Voter where
  toData
  | .CommitteeVoter cred => mkDataConstr 0 [IsData.toData cred]
  | .DRepVoter cred => mkDataConstr 1 [IsData.toData cred]
  | .StakePoolVoter pk => mkDataConstr 2 [IsData.toData pk]
  fromData
  | Data.Constr 0 [r_cred] =>
        match IsData.fromData r_cred with
        | some cred => some (.CommitteeVoter cred)
        | none => none
  | Data.Constr 1 [r_cred] =>
        match IsData.fromData r_cred with
        | some cred => some (.DRepVoter cred)
        | none => none
  | Data.Constr 2 [r_pk] =>
        match IsData.fromData r_pk with
        | some pk => some (.StakePoolVoter pk)
        | none => none
  | _ => none


/--  A vote. The optional anchor is omitted. -/
inductive Vote where
  | VoteNo : Vote
  | VoteYes : Vote
  | Abstain : Vote
deriving Repr

def beqVote (x y : Vote) : Bool :=
  match x, y with
  | .VoteNo, .VoteNo
  | .VoteYes, .VoteYes
  | .Abstain, .Abstain => true
  | _, _ => false

/-- BEq instance for Vote -/
instance : BEq Vote := ⟨beqVote⟩

/-! DecidableEq instance for Vote -/
@[simp] theorem beqVote_iff_eq (x y : Vote) : beqVote x y ↔ x = y := by
  cases x <;> cases y <;> simp [beqVote]

@[simp] theorem beqVote_false_iff_not_eq (x y : Vote) : beqVote x y = false ↔ x ≠ y := by
  cases x <;> cases y <;> simp [beqVote]

def decEqVote (x y : Vote) : Decidable (Eq x y) :=
  match h:(beqVote x y) with
  | true => isTrue ((beqVote_iff_eq _ _).1 h)
  | false => isFalse ((beqVote_false_iff_not_eq _ _).1 h)

instance : DecidableEq Vote := decEqVote

/-! LawfulBEq instance for Vote -/
theorem beqVote_reflexive (x : Vote) : beqVote x x = true := by
   cases x <;> simp [beqVote]

instance : LawfulBEq Vote where
  eq_of_beq {a b} := (beqVote_iff_eq a b).1
  rfl {bs} := by simp [BEq.beq]

def ltVote (x y : Vote) : Bool :=
  match x, y with
  | .VoteNo, .VoteNo => false
  | .VoteNo, _ => true
  | .VoteYes, .VoteNo => false
  | .VoteYes, .VoteYes => false
  | .VoteYes, _ => true
  | .Abstain, _ => false

/-- LT instance for Vote -/
instance : LT Vote where
  lt x y := ltVote x y

/-! DecidableLT instance for Vote -/
theorem ltVote_true_imp_lt (x y : Vote) : ltVote x y → x < y := by
  cases x <;> cases y <;> simp only [ltVote, LT.lt] <;> simp

theorem ltVote_false_imp_not_lt (x y : Vote) :
  ltVote x y = false → ¬ x < y := by
    cases x <;> cases y <;> simp only [ltVote, LT.lt] <;> simp

def decLtVote (x y : Vote) : Decidable (LT.lt x y) :=
  match h:(ltVote x y) with
  | true => isTrue (ltVote_true_imp_lt _ _ h)
  | false => isFalse (ltVote_false_imp_not_lt _ _ h)

instance : DecidableLT Vote := decLtVote

/-! Std.Irrefl instance for Vote -/
@[simp] theorem ltVote_same_false (x : Vote) : ltVote x x = false := by cases x <;> simp [ltVote]

theorem Vote_lt_irrefl (x : Vote) : ¬ x < x := by cases x <;> simp [LT.lt]

instance : Std.Irrefl (. < . : Vote → Vote → Prop) where
  irrefl := Vote_lt_irrefl

/-- LE instance for Vote -/
instance : LE Vote where
  le x y := ¬ (y < x)

/-! DecidableLE instance for Vote -/
instance : DecidableLE Vote :=
  fun x y => inferInstanceAs (Decidable (¬ (y < x)))

/-- IsData instance for Vote -/
instance : IsData Vote where
  toData
  | .VoteNo => mkDataConstr 0
  | .VoteYes => mkDataConstr 1
  | .Abstain => mkDataConstr 2
  fromData
  | Data.Constr idx [] =>
     if idx == 0 then some .VoteNo
     else if idx == 1 then some .VoteYes
     else if idx == 2 then some .Abstain
     else none
  | _ => none

/-- Similar to TxOutRef, but for GovActions -/
structure GovernanceActionId where
  gaidTxId : V3.TxId
  gaidGovActionIx : Integer
deriving Repr


def beqGovernanceActionId (x y : GovernanceActionId) : Bool :=
  x.gaidTxId == y.gaidTxId &&
  x.gaidGovActionIx == y.gaidGovActionIx

/-- BEq instance for GovernanceActionId -/
instance : BEq GovernanceActionId := ⟨beqGovernanceActionId⟩

/-! DecidableEq instance for GovernanceActionId -/
@[simp] theorem beqGovernanceActionId_iff_eq (x y : GovernanceActionId) : beqGovernanceActionId x y ↔ x = y := by
  cases x <;> cases y <;> simp [beqGovernanceActionId]

@[simp] theorem beqGovernanceActionId_false_iff_not_eq (x y : GovernanceActionId) : beqGovernanceActionId x y = false ↔ x ≠ y := by
  cases x <;> cases y <;> simp [beqGovernanceActionId]

def decEqGovernanceActionId (x y : GovernanceActionId) : Decidable (Eq x y) :=
  match h:(beqGovernanceActionId x y) with
  | true => isTrue ((beqGovernanceActionId_iff_eq _ _).1 h)
  | false => isFalse ((beqGovernanceActionId_false_iff_not_eq _ _).1 h)

instance : DecidableEq GovernanceActionId := decEqGovernanceActionId

/-! LawfulBEq instance for GovernanceActionId -/
theorem beqGovernanceActionId_reflexive (x : GovernanceActionId) : beqGovernanceActionId x x = true := by
   cases x <;> simp [beqGovernanceActionId]

instance : LawfulBEq GovernanceActionId where
  eq_of_beq {a b} := (beqGovernanceActionId_iff_eq a b).1
  rfl {bs} := by simp [BEq.beq]

def ltGovernanceActionId (x y : GovernanceActionId) : Bool :=
  x.gaidTxId < y.gaidTxId || (x.gaidTxId == y.gaidTxId && x.gaidGovActionIx < y.gaidGovActionIx)

/-- LT instance for GovernanceActionId -/
instance : LT GovernanceActionId where
  lt x y := ltGovernanceActionId x y

/-! DecidableLT instance for GovernanceActionId -/
theorem ltGovernanceActionId_true_imp_lt (x y : GovernanceActionId) : ltGovernanceActionId x y → x < y := by
  cases x <;> cases y <;> simp only [ltGovernanceActionId, LT.lt] <;> simp

theorem ltGovernanceActionId_false_imp_not_lt (x y : GovernanceActionId) :
  ltGovernanceActionId x y = false → ¬ x < y := by
    cases x <;> cases y <;> simp only [ltGovernanceActionId, LT.lt] <;> simp

def decLtGovernanceActionId (x y : GovernanceActionId) : Decidable (LT.lt x y) :=
  match h:(ltGovernanceActionId x y) with
  | true => isTrue (ltGovernanceActionId_true_imp_lt _ _ h)
  | false => isFalse (ltGovernanceActionId_false_imp_not_lt _ _ h)

instance : DecidableLT GovernanceActionId := decLtGovernanceActionId

/-! Std.Irrefl instance for GovernanceActionId -/
@[simp] theorem ltGovernanceActionId_same_false (x : GovernanceActionId) : ltGovernanceActionId x x = false :=
  by cases x <;> simp [ltGovernanceActionId]

theorem GovernanceActionId_lt_irrefl (x : GovernanceActionId) : ¬ x < x := by cases x <;> simp [LT.lt]

instance : Std.Irrefl (. < . : GovernanceActionId → GovernanceActionId → Prop) where
  irrefl := GovernanceActionId_lt_irrefl

/-- LE instance for GovernanceActionId -/
instance : LE GovernanceActionId where
  le x y := ¬ (y < x)

/-! DecidableLE instance for GovernanceActionId -/
instance : DecidableLE GovernanceActionId :=
  fun x y => inferInstanceAs (Decidable (¬ (y < x)))

/-- IsData instance for GovernanceActionId -/
instance : IsData GovernanceActionId where
  toData x := mkDataConstr 0 [IsData.toData x.gaidTxId, IsData.toData x.gaidGovActionIx]
  fromData
  | Data.Constr 0 [r_tid, r_idx] =>
     match IsData.fromData r_tid, IsData.fromData r_idx with
     | some tid, some idx => some ⟨tid, idx⟩
     | _, _ => none
  | _ => none


/-- A proposal procedure. The optional anchor is omitted. -/
structure ProposalProcedure where
  ppDeposit : Integer
  ppReturnAddr : V2.Credential
  ppGovernanceAction : Data -- keep at Data level
deriving Repr


def beqProposalProcedure (x y : ProposalProcedure) : Bool :=
  x.ppDeposit == y.ppDeposit &&
  x.ppReturnAddr == y.ppReturnAddr &&
  x.ppGovernanceAction == y.ppGovernanceAction

/-- BEq instance for ProposalProcedure -/
instance : BEq ProposalProcedure := ⟨beqProposalProcedure⟩

/-! DecidableEq instance for ProposalProcedure -/
@[simp] theorem beqProposalProcedure_iff_eq (x y : ProposalProcedure) : beqProposalProcedure x y ↔ x = y := by
  match x, y with
  | ProposalProcedure.mk .., ProposalProcedure.mk .. =>
      simp [beqProposalProcedure]; apply Iff.intro <;>
      . repeat' rw [and_imp];
        intros; repeat' constructor <;> repeat' assumption

@[simp] theorem beqProposalProcedure_false_iff_not_eq (x y : ProposalProcedure) : beqProposalProcedure x y = false ↔ x ≠ y := by
  cases x <;> cases y <;> simp [beqProposalProcedure]

def decEqProposalProcedure (x y : ProposalProcedure) : Decidable (Eq x y) :=
  match h:(beqProposalProcedure x y) with
  | true => isTrue ((beqProposalProcedure_iff_eq _ _).1 h)
  | false => isFalse ((beqProposalProcedure_false_iff_not_eq _ _).1 h)

instance : DecidableEq ProposalProcedure := decEqProposalProcedure

/-! LawfulBEq instance for ProposalProcedure -/
theorem beqProposalProcedure_reflexive (x : ProposalProcedure) : beqProposalProcedure x x = true := by
   cases x <;> simp [beqProposalProcedure]

instance : LawfulBEq ProposalProcedure where
  eq_of_beq {a b} := (beqProposalProcedure_iff_eq a b).1
  rfl {bs} := by simp [BEq.beq]

def ltProposalProcedure (x y : ProposalProcedure) : Bool :=
   x.ppDeposit < y.ppDeposit ||
   (x.ppDeposit == y.ppDeposit &&
    (x.ppReturnAddr < y.ppReturnAddr ||
     (x.ppReturnAddr == y.ppReturnAddr && x.ppGovernanceAction < y.ppGovernanceAction)))

/-- LT instance for ProposalProcedure -/
instance : LT ProposalProcedure where
  lt x y := ltProposalProcedure x y

/-! DecidableLT instance for ProposalProcedure -/
theorem ltProposalProcedure_true_imp_lt (x y : ProposalProcedure) : ltProposalProcedure x y → x < y := by
  cases x <;> cases y <;> simp only [ltProposalProcedure, LT.lt] <;> simp

theorem ltProposalProcedure_false_imp_not_lt (x y : ProposalProcedure) :
  ltProposalProcedure x y = false → ¬ x < y := by
    cases x <;> cases y <;> simp only [ltProposalProcedure, LT.lt] <;> simp

def decLtProposalProcedure (x y : ProposalProcedure) : Decidable (LT.lt x y) :=
  match h:(ltProposalProcedure x y) with
  | true => isTrue (ltProposalProcedure_true_imp_lt _ _ h)
  | false => isFalse (ltProposalProcedure_false_imp_not_lt _ _ h)

instance : DecidableLT ProposalProcedure := decLtProposalProcedure

/-! Std.Irrefl instance for ProposalProcedure -/
@[simp] theorem ltProposalProcedure_same_false (x : ProposalProcedure) : ltProposalProcedure x x = false := by
  match x with
  | ProposalProcedure.mk .. => simp [ltProposalProcedure]; apply V1.Credential.Credential.lt_irrefl

theorem ProposalProcedure_lt_irrefl (x : ProposalProcedure) : ¬ x < x := by cases x <;> simp [LT.lt]

instance : Std.Irrefl (. < . : ProposalProcedure → ProposalProcedure → Prop) where
  irrefl := ProposalProcedure_lt_irrefl

/-- LE instance for ProposalProcedure -/
instance : LE ProposalProcedure where
  le x y := ¬ (y < x)

/-! DecidableLE instance for ProposalProcedure -/
instance : DecidableLE ProposalProcedure :=
  fun x y => inferInstanceAs (Decidable (¬ (y < x)))

/-- IsData instance for ProposalProcedure -/
instance : IsData ProposalProcedure where
  toData x := mkDataConstr 0 [IsData.toData x.ppDeposit, IsData.toData x.ppReturnAddr, x.ppGovernanceAction]
  fromData
  | Data.Constr 0 [r_deposit, r_addr, action] =>
      match IsData.fromData r_deposit, IsData.fromData r_addr with
      | some deposit, some addr => some ⟨deposit, addr, action⟩
      | _, _ => none
  | _ => none

end CardanoLedgerApi.V3.Governance

