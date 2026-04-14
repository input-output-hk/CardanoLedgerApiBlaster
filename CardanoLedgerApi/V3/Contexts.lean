import CardanoLedgerApi.IsData.Class
import CardanoLedgerApi.V2
import CardanoLedgerApi.V3.Tx
import CardanoLedgerApi.V3.TxCert
import CardanoLedgerApi.V3.Governance
import PlutusCore

namespace CardanoLedgerApi.V3.Contexts

open IsData.Class
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.Data (Data)
open PlutusCore.UPLC.Term (Term)
open Recursors
open TxCert
open Governance

/--  Purpose of the script that is currently running -/
inductive ScriptPurpose where
  | Minting : V2.CurrencySymbol → ScriptPurpose
  | Spending : V3.TxOutRef → ScriptPurpose
  | Rewarding : V2.Credential → ScriptPurpose
  | Certifying : Integer → TxCert → ScriptPurpose
  | Voting : Voter → ScriptPurpose
  | Proposing : Integer → ProposalProcedure → ScriptPurpose
deriving Repr


def beqScriptPurpose (x y : ScriptPurpose) : Bool :=
  match x, y with
  | .Minting cs1, .Minting cs2 => cs1 == cs2
  | .Spending ref1, .Spending ref2 => ref1 == ref2
  | .Rewarding cred1, .Rewarding cred2 => cred1 == cred2
  | .Certifying n1 cert1, .Certifying n2 cert2 => n1 == n2 && cert1 == cert2
  | .Voting v1, .Voting v2 => v1 == v2
  | .Proposing n1 p1, .Proposing n2 p2 => n1 == n2 && p1 == p2
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
  | .Certifying n1 cert1, .Certifying n2 cert2 => n1 < n2 || (n1 == n2 && cert1 < cert2)
  | .Certifying .., .Voting _
  | .Certifying .., .Proposing .. => true
  | .Certifying .., _ => false
  | .Voting v1, .Voting v2 => v1 < v2
  | .Voting _, .Proposing .. => true
  | .Voting _, _ => false
  | .Proposing n1 p1, .Proposing n2 p2 => n1 < n2 || (n1 == n2 && p1 < p2)
  | .Proposing .., _ => false

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
    cases x <;> simp only [ltScriptPurpose, LT.lt] <;> simp
    . apply String.lt_irrefl
    . apply Int.lt_irrefl
    . apply Int.lt_irrefl

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
  | .Certifying n cert => mkDataConstr 3 [Data.I n, IsData.toData cert]
  | .Voting v => mkDataConstr 4 [IsData.toData v]
  | .Proposing n p => mkDataConstr 5 [Data.I n, IsData.toData p]
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
  | Data.Constr 3 [Data.I n, r_cert] =>
       match IsData.fromData r_cert with
       | some cert => some (.Certifying n cert)
       | none => none
  | Data.Constr 4 [r_v] =>
       match IsData.fromData r_v with
       | some v => some (.Voting v)
       | none => none
  | Data.Constr 5 [Data.I n, r_p] =>
       match IsData.fromData r_p with
       | some p => some (.Proposing n p)
       | none => none
  | _ => none


/-- Like `ScriptPurpose` but with an optional datum for spending scripts. -/
inductive ScriptInfo where
  | MintingScript : V2.CurrencySymbol → ScriptInfo
  | SpendingScript : V3.TxOutRef → Option V2.Datum → ScriptInfo
  | RewardingScript : V2.Credential → ScriptInfo
  | CertifyingScript : Integer → TxCert → ScriptInfo
  | VotingScript : Voter → ScriptInfo
  | ProposingScript : Integer → ProposalProcedure → ScriptInfo
deriving Repr


def beqScriptInfo (x y : ScriptInfo) : Bool :=
  match x, y with
  | .MintingScript cs1, .MintingScript cs2 => cs1 == cs2
  | .SpendingScript ref1 d1, .SpendingScript ref2 d2 => ref1 == ref2 && d1 == d2
  | .RewardingScript cred1, .RewardingScript cred2 => cred1 == cred2
  | .CertifyingScript n1 cert1, .CertifyingScript n2 cert2 => n1 == n2 && cert1 == cert2
  | .VotingScript v1, .VotingScript v2 => v1 == v2
  | .ProposingScript n1 p1, .ProposingScript n2 p2 => n1 == n2 && p1 == p2
  | _, _=> false

/-- BEq instance for ScriptInfo -/
instance : BEq ScriptInfo := ⟨beqScriptInfo⟩

/-! DecidableEq instance for ScriptInfo -/
@[simp] theorem beqScriptInfo_iff_eq (x y : ScriptInfo) : beqScriptInfo x y ↔ x = y := by
  cases x <;> cases y <;> simp [beqScriptInfo]

@[simp] theorem beqScriptInfo_false_iff_not_eq (x y : ScriptInfo) : beqScriptInfo x y = false ↔ x ≠ y := by
  cases x <;> cases y <;> simp [beqScriptInfo]

def ScriptInfo.decEq (x y : ScriptInfo) : Decidable (Eq x y) :=
  match h:(beqScriptInfo x y) with
  | true => isTrue ((beqScriptInfo_iff_eq _ _).1 h)
  | false => isFalse ((beqScriptInfo_false_iff_not_eq _ _).1 h)

instance : DecidableEq ScriptInfo := ScriptInfo.decEq

/-! LawfulBEq instance for ScriptInfo -/
theorem beqScriptInfo_reflexive (x : ScriptInfo) : beqScriptInfo x x = true := by
   cases x <;> simp [beqScriptInfo]

instance : LawfulBEq ScriptInfo where
  eq_of_beq {a b} := (beqScriptInfo_iff_eq a b).1
  rfl {bs} := by simp [BEq.beq]


/-- IsData instance for ScriptPurpose -/
instance : IsData ScriptInfo where
  toData
  | .MintingScript cs => mkDataConstr 0 [IsData.toData cs]
  | .SpendingScript ref dat => mkDataConstr 1 [IsData.toData ref, IsData.toData dat]
  | .RewardingScript cred => mkDataConstr 2 [IsData.toData cred]
  | .CertifyingScript n cert => mkDataConstr 3 [Data.I n, IsData.toData cert]
  | .VotingScript v => mkDataConstr 4 [IsData.toData v]
  | .ProposingScript n p => mkDataConstr 5 [IsData.toData n, IsData.toData p]
  fromData
  | Data.Constr 0 [Data.B cs] => some (.MintingScript cs)
  | Data.Constr 1 [r_ref, r_dat] =>
       match IsData.fromData r_ref, IsData.fromData r_dat with
       | some ref, some dat => some (.SpendingScript ref dat)
       | _, _ => none
  | Data.Constr 2 [r_cred] =>
       match IsData.fromData r_cred with
       | some cred => some (.RewardingScript cred)
       | none => none
  | Data.Constr 3 [Data.I n, r_cert] =>
       match IsData.fromData r_cert with
       | some cert => some (.CertifyingScript n cert)
       | none => none
  | Data.Constr 4 [r_v] =>
       match IsData.fromData r_v with
       | some v => some (.VotingScript v)
       | none => none
  | Data.Constr 5 [Data.I n, r_p] =>
       match IsData.fromData r_p with
       | some p => some (.ProposingScript n p)
       | none => none
  | _ => none

/-- An input of a pending transaction -/
structure TxInInfo where
  txInInfoOutRef : V3.TxOutRef
  txInInfoResolved : V2.TxOut
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

/-- Unlike V1/V2, MintValue does not contain Ada with zero quantity -/
abbrev MintValue := V2.Value

abbrev Withdrawals := List (V2.Credential × Integer) -- handled as a Data.Map at the Data level

/-- Return the list `Data × Data` representation for Withdrawals. -/
def withdrawalsToListPairData (xs : Withdrawals) : List (Data × Data) :=
  Recursor.map x in xs with (IsData.toData x.1, Data.I x.2)

/-- Try to decode `Withdrawals` from a `Data × Data` list instance. -/
def listPairDataToWithdrawals (xs : List (Data × Data)) : Option Withdrawals :=
  match xs with
  | [] => some []
  | (d1, Data.I i) :: xs' =>
      match IsData.fromData d1, listPairDataToWithdrawals xs' with
      | some cred, some rest => (cred, i) :: rest
      | _, _ => none
  | _ => none

/-- IsData instance for Withdrawals -/
instance : IsData Withdrawals where
  toData x := Data.Map (withdrawalsToListPairData x)
  fromData
  | Data.Map r_wdrwl => listPairDataToWithdrawals r_wdrwl
  | _ => none

abbrev RedeemerMap := List (ScriptPurpose × V2.Redeemer) -- handled as a Data.Map at the Data level

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

abbrev GovernanceVoteMap := List (GovernanceActionId × Vote) -- handled as a Data.Map at the Data level

/-- Return the list `Data × Data` representation for GovernanceVoteMap. -/
def governanceVoteMapToListPairData (xs : GovernanceVoteMap) : List (Data × Data) :=
  Recursor.map x in xs with (IsData.toData x.1, IsData.toData x.2)

/-- Try to decode `GovernanceVoteMap` from a `Data × Data` list instance. -/
def listPairDataToGovernanceVoteMap (xs : List (Data × Data)) : Option GovernanceVoteMap :=
  match xs with
  | [] => some []
  | (r_action, r_vote) :: xs' =>
      match IsData.fromData r_action, IsData.fromData r_vote, listPairDataToGovernanceVoteMap xs' with
      | some action, some vote, some rest => (action, vote) :: rest
      | _, _, _ => none

/-- IsData instance for GovernanceVoteMap -/
instance : IsData GovernanceVoteMap where
  toData x := Data.Map (governanceVoteMapToListPairData x)
  fromData
  | Data.Map r_map => listPairDataToGovernanceVoteMap r_map
  | _ => none


abbrev VoterMap := List (Voter × GovernanceVoteMap) -- handled as a Data.Map at the Data level

/-- Return the list `Data × Data` representation for VoterMap. -/
def voterMapToListPairData (xs : VoterMap) : List (Data × Data) :=
  Recursor.map x in xs with (IsData.toData x.1, IsData.toData x.2)

/-- Try to decode `VoterMap` from a `Data × Data` list instance. -/
def listPairDataToVoterMap (xs : List (Data × Data)) : Option VoterMap :=
  match xs with
  | [] => some []
  | (r_voter, r_governance) :: xs' =>
      match IsData.fromData r_voter, IsData.fromData r_governance, listPairDataToVoterMap xs' with
      | some voter, some governance, some rest => (voter, governance) :: rest
      | _, _, _ => none

/-- IsData instance for VoterMap -/
instance : IsData VoterMap where
  toData x := Data.Map (voterMapToListPairData x)
  fromData
  | Data.Map r_map => listPairDataToVoterMap r_map
  | _ => none


/-- TxInfo for PlutusV3 -/
structure TxInfo where
  /-- Transaction's inputs: cannot be an empty list. -/
  txInfoInputs : List TxInInfo
  /-- Transaction's reference inputs. -/
  txInfoReferenceInputs : List TxInInfo
  /-- Transaction's outputs -/
  txInfoOutputs : List V2.TxOut
  /-- The fee paid by this transaction. -/
  txInfoFee : Integer
  /-- The `Value` minted by this transaction -/
  txInfoMint : MintValue
  /-- Digests of certificates included in this transaction. -/
  txInfoTxCerts : List TxCert
  /-- Withdrawals -/
  txInfoWdrl : Withdrawals
  /-- The valid range for the transaction. -/
  txInfoValidRange : Data -- keep at Data level
  /-- Signers of the transaction. -/
  txInfoSignatories : List V2.PubKeyHash
  /-- The lookup table for redeemers attached to the transaction. -/
  txInfoRedeemers : RedeemerMap
  /-- The lookup table of datums attached to the transaction. -/
  txInfoData : V2.DatumMap
  /-- ^ Hash of the pending transaction body (i.e. transaction excluding witnesses) -/
  txInfoId : V3.TxId
  txInfoVotes : VoterMap
  txInfoProposalProcedures : List ProposalProcedure
  txInfoCurrentTreasuryAmount : Data -- keep at Data level
  txInfoTreasuryDonation : Data -- keep at Data level
deriving Repr

def beqTxInfo (x y : TxInfo) : Bool :=
  x.txInfoInputs == y.txInfoInputs &&
  x.txInfoReferenceInputs == y.txInfoReferenceInputs &&
  x.txInfoOutputs == y.txInfoOutputs &&
  x.txInfoFee == y.txInfoFee &&
  x.txInfoMint == y.txInfoMint &&
  x.txInfoTxCerts == y.txInfoTxCerts &&
  x.txInfoWdrl == y.txInfoWdrl &&
  x.txInfoValidRange == y.txInfoValidRange &&
  x.txInfoSignatories == y.txInfoSignatories &&
  x.txInfoRedeemers == y.txInfoRedeemers &&
  x.txInfoData == y.txInfoData &&
  x.txInfoId == y.txInfoId &&
  x.txInfoVotes == y.txInfoVotes &&
  x.txInfoProposalProcedures == y.txInfoProposalProcedures &&
  x.txInfoCurrentTreasuryAmount == y.txInfoCurrentTreasuryAmount &&
  x.txInfoTreasuryDonation == y.txInfoTreasuryDonation

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

/-- Return the list `Data` representation for the given `ProposalProcedure` list. -/
def txInfoProposalProcsToListData (xs : List ProposalProcedure) : List Data :=
  Recursor.map x in xs with IsData.toData x

/-- Try to decode `ProposalProcedure` list from a `Data` list instance. -/
def listDataToTxInfoProposalProcs (xs : List Data) : Option (List ProposalProcedure) :=
  match xs with
  | [] => some []
  | x :: xs' =>
      match IsData.fromData x, listDataToTxInfoProposalProcs xs' with
      | some out, some rest => out :: rest
      | _, _ => none

/-- IsData instance for List ProposalProcedure -/
instance : IsData (List ProposalProcedure) where
  toData procedures := Data.List (txInfoProposalProcsToListData procedures)
  fromData
  | Data.List r_procedures => listDataToTxInfoProposalProcs r_procedures
  | _ => none

/-- Return the list `Data` representation for the given `TxCert` list. -/
def txInfoTxCertsToListData (xs : List TxCert) : List Data :=
  Recursor.map x in xs with IsData.toData x

/-- Try to decode `TxCert` list from a `Data` list instance. -/
def listDataToTxInfoTxCerts (xs : List Data) : Option (List TxCert) :=
  match xs with
  | [] => some []
  | x :: xs' =>
      match IsData.fromData x, listDataToTxInfoTxCerts xs' with
      | some out, some rest => out :: rest
      | _, _ => none

/-- IsData instance for List TxCert -/
instance : IsData (List TxCert) where
  toData certs := Data.List (txInfoTxCertsToListData certs)
  fromData
  | Data.List r_certs => listDataToTxInfoTxCerts r_certs
  | _ => none

/-- IsData instance for TxInfo -/
instance : IsData TxInfo where
  toData info :=
    mkDataConstr 0
    [ IsData.toData info.txInfoInputs
    , IsData.toData info.txInfoReferenceInputs
    , IsData.toData info.txInfoOutputs
    , Data.I info.txInfoFee
    , IsData.toData info.txInfoMint
    , IsData.toData info.txInfoTxCerts
    , IsData.toData info.txInfoWdrl
    , IsData.toData info.txInfoValidRange
    , IsData.toData info.txInfoSignatories
    , IsData.toData info.txInfoRedeemers
    , IsData.toData info.txInfoData
    , IsData.toData info.txInfoId
    , IsData.toData info.txInfoVotes
    , IsData.toData info.txInfoProposalProcedures
    , IsData.toData info.txInfoCurrentTreasuryAmount
    , IsData.toData info.txInfoTreasuryDonation
    ]
  fromData
  | Data.Constr 0 [r_ins, r_refs, r_outs, Data.I fees, r_mint, r_certs, r_wdrwl,
                   r_range, r_sig, r_redeemers, r_dat, r_tid, r_votes, r_proposals, r_amount, r_donation] =>
     match IsData.fromData r_ins, IsData.fromData r_refs, IsData.fromData r_outs, IsData.fromData r_mint,
           IsData.fromData r_certs, IsData.fromData r_wdrwl,
           IsData.fromData r_range, IsData.fromData r_sig,
           IsData.fromData r_redeemers, IsData.fromData r_dat,
           IsData.fromData r_tid, IsData.fromData r_votes,
           IsData.fromData r_proposals, IsData.fromData r_amount, IsData.fromData r_donation with
    | some ins, some refs, some outs, some mint, some certs,
      some wdrwl, some range, some sigs, some redeemers, some dat, some tid,
      some votes, some proposals, some amount, some donation =>
       some ⟨ins, refs, outs, fees, mint, certs, wdrwl, range, sigs, redeemers, dat, tid, votes, proposals, amount, donation⟩
    |_, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | _ => none

/-- The context that the currently-executing script can access. -/
structure ScriptContext where
  scriptContextTxInfo : TxInfo
  scriptContextRedeemer : V2.Redeemer
  scriptContextScriptInfo : ScriptInfo
deriving Repr


def beqScriptContext (x y : ScriptContext) : Bool :=
  x.scriptContextTxInfo == y.scriptContextTxInfo &&
  x.scriptContextRedeemer == y.scriptContextRedeemer &&
  x.scriptContextScriptInfo == y.scriptContextScriptInfo

/-- BEq instance for ScriptContext -/
instance : BEq ScriptContext := ⟨beqScriptContext⟩

/-! DecidableEq instance for ScriptContext -/
@[simp] theorem beqScriptContext_iff_eq (x y : ScriptContext) : beqScriptContext x y ↔ x = y := by
  match x, y with
  | ScriptContext.mk .., ScriptContext.mk .. =>
      simp [beqScriptContext]; apply Iff.intro <;>
      . repeat' rw [and_imp];
        intros; repeat' constructor <;> repeat' assumption

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
  toData ctx := mkDataConstr 0 [IsData.toData ctx.scriptContextTxInfo,
                                ctx.scriptContextRedeemer,
                                IsData.toData ctx.scriptContextScriptInfo]
  fromData
  | Data.Constr 0 [r_infos, redeemer, r_sinfo] =>
      match IsData.fromData r_infos, IsData.fromData r_sinfo with
      | some tinfos, some sinfo => some ⟨tinfos, redeemer, sinfo⟩
      | _, _ => none
  | _ => none

-- /-! Helpers -/

/-- Find the `TxInInfo` corresponding to the given `TxOutRef` in a list of inputs. -/
def resolveInput (utxo : V3.TxOutRef) (inputs : List TxInInfo) : Option TxInInfo :=
  Recursor.findMap? x in inputs => x.txInInfoOutRef == utxo with x

/-- Find the spending script's own input and return the corresponding `TxInInfo`, if present.
    Return `none` when script purpose is not `Spending`.
-/
def findOwnInput (ctx : ScriptContext) : Option TxInInfo :=
  match ctx.scriptContextScriptInfo with
  | .SpendingScript ownTxOutRef _ => resolveInput ownTxOutRef ctx.scriptContextTxInfo.txInfoInputs
  | _ => none

/-- Find all inputs associated to the given public key hash. -/
def findPubKeyInputs (pk : V2.PubKeyHash) (inputs : List TxInInfo) : List TxInInfo :=
  Recursor.findAll x in inputs => V2.hasPubKeyAddress pk x.txInInfoResolved

/-- Find all inputs associated to the given script hash. -/
def findScriptInputs (sh : V2.ScriptHash) (inputs : List TxInInfo) : List TxInInfo :=
  Recursor.findAll x in inputs => V2.hasScriptAddress sh x.txInInfoResolved

/-- Return the first input satisfying predicate f, if present. -/
def findInput (f : TxInInfo → Bool) (inputs : List TxInInfo) : Option TxInInfo :=
  Recursor.find? x in inputs => f x

/-- Find a redeemer according to the given script purpose, if present in the redeemer map. -/
def findRedeemer (purpose : ScriptPurpose) (redeemers : RedeemerMap) : Option V2.Redeemer :=
  Recursor.findMap? x in redeemers => x.1 == purpose with x.2

/-- Return the `CurrencySymbol` of the current validator script only when script purpose is `Minting`. -/
def ownCurrencySymbol (ctx : ScriptContext) : Option V2.CurrencySymbol :=
  match ctx.scriptContextScriptInfo with
  | .MintingScript cs => some cs
  | _ => none

/-- Return the total value of inputs spent in the pending transaction -/
def valueSpent (ctx : ScriptContext) : V2.Value :=
  let rec visit (ins : List TxInInfo) (acc : V2.Value) : V2.Value :=
    match ins with
    | [] => acc
    | x :: xs => visit xs (V2.merge x.txInInfoResolved.txOutValue acc)
  visit ctx.scriptContextTxInfo.txInfoInputs V2.null


/-- Return the total value of inputs produced by the pending transaction -/
def valueProduced (ctx : ScriptContext) : V2.Value :=
  let rec visit (outs : List V2.TxOut) (acc : V2.Value) : V2.Value :=
    match outs with
    | [] => acc
    | x :: xs => visit xs (V2.merge x.txOutValue acc)
  visit ctx.scriptContextTxInfo.txInfoOutputs V2.null


/-- Convert a `ScriptInfo` to a `ScriptPurpose`. -/
def ScriptInfo.toScriptPurpose : ScriptInfo → ScriptPurpose
  | .MintingScript cs => .Minting cs
  | .SpendingScript tref _ => .Spending tref
  | .RewardingScript cred => .Rewarding cred
  | .CertifyingScript n cert => .Certifying n cert
  | .VotingScript v => .Voting v
  | .ProposingScript n p => .Proposing n p


/-- Return the list of arguments to be applied to a UPLC Spending validator -/
def spendingInputs (ctx : ScriptContext) : List Term := [toTerm ctx]

/-- Return the list of arguments to be applied to a UPLC Minting validator -/
def mintingInputs (ctx : ScriptContext) : List Term := spendingInputs ctx

/-- Return the list of arguments to be applied to a UPLC Rewarding validator -/
def rewardingInputs (ctx : ScriptContext) : List Term := spendingInputs ctx

/-- Return the list of arguments to be applied to a UPLC Certifying validator -/
def certifyingInputs (ctx : ScriptContext) : List Term := spendingInputs ctx

/-- Return the list of arguments to be applied to a UPLC Voting validator -/
def votingInputs (ctx : ScriptContext) : List Term := spendingInputs ctx

/-- Return the list of arguments to be applied to a UPLC Proposing validator -/
def proposingInputs (ctx : ScriptContext) : List Term := spendingInputs ctx


/-! Predicates -/

/-- Return `true` only when the script info is `MintingScript`. -/
def isMintingScriptInfo (ctx : ScriptContext) : Bool :=
  match ctx.scriptContextScriptInfo with
  | .MintingScript _ => true
  | _ => false

/-- Return `true` only when the script info is `RewardingScript`. -/
def isRewardingScriptInfo (ctx : ScriptContext) : Bool :=
  match ctx.scriptContextScriptInfo with
  | .RewardingScript _  => true
  | _ => false

/-- Return `true` only when the script info is `SpendingScript`. -/
def isSpendingScriptInfo (ctx : ScriptContext) : Bool :=
  match ctx.scriptContextScriptInfo with
  | .SpendingScript ..  => true
  | _ => false

/-- Return `true` only when the script info is `CertifyingScript`. -/
def isCertifyingScriptInfo (ctx : ScriptContext) : Bool :=
  match ctx.scriptContextScriptInfo with
  | .CertifyingScript ..  => true
  | _ => false

/-- Return `true` only when the script info is `VotingScript`. -/
def isVotingScriptInfo (ctx : ScriptContext) : Bool :=
  match ctx.scriptContextScriptInfo with
  | .VotingScript ..  => true
  | _ => false

/-- Return `true` only when the script info is `ProposingScript`. -/
def isProposingScriptInfo (ctx : ScriptContext) : Bool :=
  match ctx.scriptContextScriptInfo with
  | .ProposingScript ..  => true
  | _ => false

/-- Check if the given `TxOutRef` is present in the list of inputs. -/
def utxoConsumed (utxo : V3.TxOutRef) (inputs : List TxInInfo) : Bool :=
  Recursor.any x in inputs => x.txInInfoOutRef == utxo

/-- Check if a transaction was signed by the given public key hash. -/
def txSignedBy (pk : V2.PubKeyHash) (tx : TxInfo) : Bool :=
  Recursor.any x in tx.txInfoSignatories => x == pk

/-- Check if the given public key hash is the only signatory. -/
def onlySingedBy (pk : V2.PubKeyHash) (tx : TxInfo) : Bool :=
  tx.txInfoSignatories == [pk]

/-- Check if the given credential is present in the withdrawal map. -/
def credentialInWithdrawals (cred : V2.Credential) (withdrawals : Withdrawals) : Bool :=
  Recursor.any x in withdrawals => x.1 == cred

/-- Check if the given certificate is present in the `TxCert` list at index `idx`. -/
def isKnownCertificate (cert : TxCert) (idx : Integer) (certificates : List TxCert) : Bool :=
  if idx < 0 then false
  else match certificates[idx.toNat]? with
       | some x => x == cert
       | none => false

/-- Check if the given proposal procedure is present in the `ProposalProcedure` list at index `idx`. -/
def isKnownProposal (prop : ProposalProcedure) (idx : Integer) (proposals : List ProposalProcedure) : Bool :=
  if idx < 0 then false
  else match proposals[idx.toNat]? with
       | some x => x == prop
       | none => false

/-- Check if the given voter is present in the Votes map. -/
def isKnownVoter (v : Voter) (votes : VoterMap) : Bool :=
  Recursor.any x in votes => x.1 == v

/-- [LEDGER-RULE]: Ledger rules for Value in TxInfoMint (V3):
    A Value `v` is valid if and only if it has the form
     v = [ (cs₁ [(tn₍₁₎₍₁₎, n₍₁₎₍₁₎), ..., (tn₍₁₎₍ₖ₁₎, n₍₁₎₍ₖ₁₎)]), ...,
           (csₘ [(tn₍ₘ₎₍₁₎, n₍ₘ₎₍₁₎), ..., (tn₍₁₎₍ₖₘ₎, n₍₁₎₍ₖₘ₎)]) ]

     such that:
       1. No Ada Value, i.e.,
           - adaSymbol < cs₁

       2. All currency symbols are sorted
          - cs₁ < cs₂ < ... < csₘ

       3. ∀ i ∈ [1..m], csᵢ has at least one token such that:
           - kᵢ ≥ 1 ∧
           - tn₍ᵢ₎₍₁₎ < tn₍ᵢ₎₍₂₎ < ... < tn₍ᵢ₎₍ₖᵢ₎ (i.e., token names are sorted)
           - ∀ j ∈ [1..kᵢ], n₍ᵢ₎₍ⱼ₎ ≠ 0 (i.e., not null quantity)
-/
def validMintValue (v : MintValue) : Bool :=
  let rec validMintTokens (tns : List (Data × Data)) (prev_tn : ByteString) : Bool :=
    match tns with
    | [] => true
    | (Data.B tn, Data.I n) :: xs => prev_tn < tn && n != 0 && validMintTokens xs tn
    | _ => false
  let rec validCurrencySymbol (v : MintValue) (prev_cs : ByteString) : Bool :=
    match v with
    | [] => true
    | (Data.B cs, Data.Map ((Data.B tn, Data.I n) :: tokens)) :: xs =>
         prev_cs < cs && n != 0 && validMintTokens tokens tn && validCurrencySymbol xs cs
    | _ => false
  validCurrencySymbol v V2.adaSymbol

/-- [LEDGER-RULE]: Ledger rules for the optional optDatum of the current spending script (V3).
     Optional optDatum is valid if and only if the following conditions are satisfied:

     1. optDatum = none →
          ¬ hasDatum ownResolvedInput ∨
          ( txOutDatumHash ownResolvedInput = some dh ∧
            ¬ ∃ datum : Datum, (dh, datum) ∈ ctx.scriptContextTxInfo.txInfoData )

     2. optDatum = some datum → txOutInlineDatum ownResolvedInput = some datum

     with:
       - optDatum : corresponding to the optional datum of the current spending script.
       - ownResolvedInput : corresponding to the resolved input `TxOut` for the current spending script.
       - ctx : corresponding to the ScriptContext applied to the current spending script.

    NOTE: For V3, optional datum for the spending script is set to `none` when
     - no datum is specified at the spending script utxo; OR
     - a datum hash is present at the spending script utxo but does NOT have a corresponding entry in the witness map.
-/
def validInputDatum (optDatum : Option V2.Datum) (ownResolvedInput : V2.TxOut) (ctx : ScriptContext) : Bool :=
  match optDatum, ownResolvedInput.txOutDatum with
  | none, .OutputDatum _ => false
  | none, .OutputDatumHash dh => V2.findDatum dh ctx.scriptContextTxInfo.txInfoData == none
  | none, .NoOutputDatum => true
  | some datum, .OutputDatum datum' => datum == datum'
  | some _, _ => false

/-- [LEDGER-RULE]: Ledger rules for the certificate of the current certifying script (V3).
    Certificate `cert` is valid if and only if one of the following conditions is satisfied:

    1. cert = TxCertRegStaking cred (some n) ∧ isScriptCredential cred -- must have a deposit

    2. cert = TxCertUnRegStaking cred _ ∧ isScriptCredential cred

    3. cert = TxCertDelegStaking cred _ ∧ isScriptCredential cred

    4. cert = TxCertRegDeleg cred _ _ ∧ isScriptCredential cred

    5. cert = TxCertRegDRep cred _ ∧ isScriptCredential cred

    6. cert = TxCertUpdateDRep cred ∧ isScriptCredential cred

    7. cert = TxCertUnRegDRep cred _ ∧ isScriptCredential cred

    8. cert = TxCertAuthHotCommittee cold _ ∧ isScriptCredential cold

    9. cert = TxCertResignColdCommittee cold ∧ isScriptCredential cold

-/
def validScriptCertificate (cert : TxCert) : Bool :=
  match cert with
  | .TxCertRegStaking cred (some _)
  | .TxCertUnRegStaking cred _
  | .TxCertDelegStaking cred _
  | .TxCertRegDeleg cred _ _
  | .TxCertRegDRep cred _
  | .TxCertUpdateDRep cred
  | .TxCertUnRegDRep  cred _
  | .TxCertAuthHotCommittee cred _
  | .TxCertResignColdCommittee cred => V2.isScriptCredential cred
  | _ => false


/-- [LEDGER-RULE]: Ledger rules for the voter of the current voting script (V3).
    Voter `v` is valid if and only if one of the following conditions is satisfied:

    1. v = CommitteeVoter cred ∧ isScriptCredential cred

    2. v = DRepVoter cred ∧ isScriptCredential cred

-/
def validScriptVoter (v : Voter) : Bool :=
  match v with
  | .CommitteeVoter cred
  | .DRepVoter cred => V2.isScriptCredential cred
  | _ => false

/-- [LEDGER-RULE]: Ledger rules for the proposal procedure of certificate of the current proposing script (V3).
    The proposal `p` is valid if and only if one of the following conditions is satisfied:

    1. p.ppGovernanceAction = ParameterChange _ _ (Just sh)

    2. p.ppGovernanceAction = TreasuryWithdrawals _ (Just sh)

-/
def validScriptProposal (p : ProposalProcedure) : Bool :=
  match p.ppGovernanceAction with
  | Data.Constr 0 [_action, _changedParams, r_hash] =>
      -- ParameterChange
      (IsData.fromData r_hash : Option V2.ScriptHash).isSome
  | Data.Constr 2 [_credMap, r_hash] =>
      -- TreasuryWithdrawals
      (IsData.fromData r_hash : Option V2.ScriptHash).isSome
  | _ => false


/-- [LEDGER-RULE]: Ledger rules for ScriptInfo (V3):
     ScriptInfo `s` is valid if and only if the following conditions are satisfied:

     1. (s.toScriptPurpose, ctx.scriptContextRedeemer) ∈ ctx.scriptContextTxInfo.txInfoRedeemers

     2. s = SpendingScript ownTxOutRef optDatum →
          ∃ x ∈ ctx.scriptContextTxInfo.txInfoInputs,
             x.txInInfoOutRef = ownTxOutRef ∧
             isScriptCredentialAddress x.txInInfoResolved.txOutAddress ∧
             validInputDatum optDatum x.txInInfoResolved ctx

     3. s = MintingScript cs → hasCurrencySymbol cs ctx.scriptContextTxInfo.txInfoMint

     4. s = RewardingScript cred →
            isScriptCredential cred ∧
            ∃ n : Integer, (cred, n) ∈ ctx.scriptContextTxInfo.txInfoWdrl

     5. s = CertifyingScript idx cert →
             validScriptCertificate cert ∧
             idx ≥ 0 ∧
             some cert = ctx.scriptContextTxInfo.txInfoDCert[idx]?

     6. s = VotingScript v →
             validScriptVoter v ∧
             ∃ gmap : GovernanceVoteMap, (v, gmap) ∈ ctx.scriptContextTxInfo.txInfoVotes

     7. s = ProposingScript idx proposal →
              validScriptProposal proposal ∧
              idx ≥ 0 ∧
              some proposal = ctx.scriptContextTxInfo.txInfoProposalProcedures[idx]?
     with:
       - ctx : corresponding to the ScriptContext applied to the current validator script.
-/
def validScriptInfo (ctx : ScriptContext) : Bool :=
  let validPurpose :=
    match ctx.scriptContextScriptInfo with
    | .SpendingScript ownTxOutRef datum =>
         if let some tin := resolveInput ownTxOutRef ctx.scriptContextTxInfo.txInfoInputs
         then V2.isScriptCredentialAddress tin.txInInfoResolved.txOutAddress &&
              validInputDatum datum tin.txInInfoResolved ctx
         else false
    | .MintingScript cs => V2.hasCurrencySymbol cs ctx.scriptContextTxInfo.txInfoMint
    | .RewardingScript cred =>
           V2.isScriptCredential cred &&
           credentialInWithdrawals cred ctx.scriptContextTxInfo.txInfoWdrl
    | .CertifyingScript idx cert =>
           validScriptCertificate cert &&
           isKnownCertificate cert idx ctx.scriptContextTxInfo.txInfoTxCerts
    | .VotingScript v =>
           validScriptVoter v &&
           isKnownVoter v ctx.scriptContextTxInfo.txInfoVotes
    | .ProposingScript idx proposal =>
           validScriptProposal proposal &&
           isKnownProposal proposal idx ctx.scriptContextTxInfo.txInfoProposalProcedures
  let purpose := ctx.scriptContextScriptInfo.toScriptPurpose
  findRedeemer purpose ctx.scriptContextTxInfo.txInfoRedeemers == some ctx.scriptContextRedeemer &&
  validPurpose


/-- [LEDGER-RULE]: Ledger rules for transaction's inputs (V3):
      Let ctx.scriptContextTxInfo.txInfoInputs = [in₁, in₂ ..., inₘ],
      the transaction's inputs are valid if and only if the following conditions are satisfied:
        1. Transaction has at least one input, i.e.,  m ≥ 1

        2. Inputs are sorted according to `TxOutRef`
            - in₁.txInInfoOutRef < in₂.txInInfoOutRef < .. < inₘ.txInInfoOutRef

        3. ∀ i ∈ [1..m],
             validTxOutValue inᵢ.txInInfoResolved.txOutValue
     with:
       - ctx : corresponding to the ScriptContext applied to the current validator script.

     NOTE: For V3, a spending script may have a datum hash without any corresponding entry in the witness map
     (see `validInputDatum`).
-/
def validInputs (ctx : ScriptContext) : Bool :=
  let rec visit (ins : List TxInInfo) (prevTxOutRef : V3.TxOutRef) : Bool :=
    match ins with
    | [] => true
    | x :: xs' => prevTxOutRef < x.txInInfoOutRef &&
                  V2.validTxOutValue x.txInInfoResolved.txOutValue &&
                  visit xs' x.txInInfoOutRef
  match ctx.scriptContextTxInfo.txInfoInputs with
  | [] => false -- at least one input expected
  | x :: xs => V2.validTxOutValue x.txInInfoResolved.txOutValue && visit xs x.txInInfoOutRef



/-- [LEDGER-RULE]: Ledger rules for transaction's reference inputs (V3):
    The transaction's reference inputs are valid if and only if one of following conditions is satisfied:
      1. Reference input list is empty
           - ctx.scriptContextTxInfo.txInfoReferenceInputs = []

      2. Reference input list is not empty such that:
          2.1 ctx.scriptContextTxInfo.txInfoReferenceInputs = [in₁, in₂ ..., inₘ]

          2.2 Reference Inputs are sorted according to `TxOutRef`
               - in₁.txInInfoOutRef < in₂.txInInfoOutRef < .. < inₘ.txInInfoOutRef

          2.3. ∀ i ∈ [1..m], validTxOutValue inᵢ.txInInfoResolved.txOutValue
     with:
       - ctx : corresponding to the ScriptContext applied to the current validator script.

     NOTE: For V3, a spending script may have a datum hash without any corresponding entry in the witness map
     (see `validInputDatum`).
-/
def validReferenceInputs (ctx : ScriptContext) : Bool :=
  let rec visit (references : List TxInInfo) (prevTxOutRef : V3.TxOutRef) : Bool :=
    match references with
    | [] => true
    | x :: xs' => prevTxOutRef < x.txInInfoOutRef &&
                  V2.validTxOutValue x.txInInfoResolved.txOutValue &&
                  visit xs' x.txInInfoOutRef
  match ctx.scriptContextTxInfo.txInfoReferenceInputs with
  | [] => true
  | x :: xs => V2.validTxOutValue x.txInInfoResolved.txOutValue && visit xs x.txInInfoOutRef


/-- [LEDGER-RULE]: Ledger rules for transaction's outputs (V3):
      - ∀ x ∈ ctx.scriptContextTxInfo.txInfoOutputs,
           validTxOutValue x.txOutValue
     with:
       - ctx : corresponding to the ScriptContext applied to the current validator script.

     NOTE: For V3, a spending script may not have any datum.
-/
def validOutputs (outputs : List V2.TxOut) : Bool :=
  Recursor.all x in outputs => V2.validTxOutValue x.txOutValue


/-- [LEDGER-RULE]: Ledger rules for transaction's Withdrawals (V3).
    The withdrawal map is valid if and only if one of the following conditions is satisfied:
      1. Withdrawal map is empty
          - ctx.scriptContextTxInfo.txInfoWdrl = []
      2. Withdrawal map is sorted w.r.t. Credential
          ctx.scriptContextTxInfo.txInfoWdrl = [(cred₁, n₁), ..., (credₖ, nₖ)] ∧
          cred₁ < cred₂ < .. < credₖ
-/
def validWithdrawals (withdrawals : Withdrawals) : Bool :=
  let rec visit (withdrawals : Withdrawals) (prev_cred : V2.Credential) : Bool :=
   match withdrawals with
   | [] => true
   | x :: xs => prev_cred < x.1 && visit xs x.1
  match withdrawals with
  | [] => true
  | x :: xs => visit xs x.1

/-- [LEDGER-RULE]: Ledger rules for transaction's redeemer map (V3).
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


/-- [LEDGER-RULE]: Ledger rules for transaction's governance vote map (V3).
    The governance vote map is valid if and only if one of the following conditions is satisfied:
      1. GovernanceVote map cannot be empty
      2. GovernanceVote map is sorted w.r.t. GovernanceActionId
          map = [(a₁, vote₁), ..., (aₙ, voteₙ)] ∧
          a₁ < a₂ < .. < aₙ
-/
def validGovernanceVoteMap (g : GovernanceVoteMap) : Bool :=
  let rec visit (g : GovernanceVoteMap) (prev_a : GovernanceActionId) : Bool :=
    match g with
    | [] => true
    | x :: xs => prev_a < x.1 && visit xs x.1
  match g with
  | [] => false -- cannot be empty
  | x :: xs => visit xs x.1

/-- [LEDGER-RULE]: Ledger rules for transaction's voter map (V3).
    The voter map is valid if and only if one of the following conditions is satisfied:
      1. Voter map is empty
          - ctx.scriptContextTxInfo.txInfoVotes = []
      2. Voter map is sorted w.r.t. Voter,
          - ctx.scriptContextTxInfo.txInfoVotes = [(v₁, g₁), ..., (vₙ, gₙ)] ∧
            v₁ < v₂ < .. < vₙ ∧
            ∀ i ∈ [1..n], validGovernanceVoteMap gᵢ
-/
def validVoterMap (votes : VoterMap) : Bool :=
  let rec visit (votes : VoterMap) (prev_v : Voter) : Bool :=
   match votes with
   | [] => true
   | x :: xs => prev_v < x.1 && validGovernanceVoteMap x.2 && visit xs x.1
  match votes with
  | [] => true
  | x :: xs => visit xs x.1

/-- [LEDGER-RULE]: Ledger rules applied to transaction's treasury amount:
    The treasury amount is valid if and only if one of the following conditions is satisfied:
    1. Treasury amount is not specified
    2. Treasury amount is specified and must be greater than zero
-/
def validTreasuryAmount (r_amount : Data) : Bool :=
  match (IsData.fromData r_amount : Option Integer) with
  | none => true
  | some n => n > 0

/-- [LEDGER-RULE]: Ledger rules applied to transaction's treasury donation:
    The treasury donation is valid if and only if one of the following conditions is satisfied:
    1. Treasury donation is not specified
    2. Treasury donation is specified and must be greater than zero
-/
def validTreasuryDonation (r_amount : Data) : Bool :=
  match (IsData.fromData r_amount : Option Integer) with
  | none => true
  | some n => n > 0

/-- [LEDGER-RULE]: A V3 pending transaction is balanced if and only if:
      - Value in inputs + txInfoMint = Value in outputs + txInfoFees
-/
def isBalanced (ctx : ScriptContext) : Bool :=
  let sv := valueSpent ctx
  let pv := valueProduced ctx
  V2.lovelaceOf sv = V2.lovelaceOf pv + ctx.scriptContextTxInfo.txInfoFee &&
  V2.merge (V2.withoutLovelace sv) ctx.scriptContextTxInfo.txInfoMint == V2.withoutLovelace pv


/-- [LEDGER-RULE]: Ledger rules for a pending transaction (V2):
    1. All transaction's inputs are valid, i.e.,
        - validInputs ctx

    2. All transaction's reference inputs are valid, i.e.,
        - validReferenceInputs ctx

    3. All transaction's outputs are valid, i.e.,
        - validOutputs ctx.scriptContextTxInfo.txInfoOutputs

    4. ctx.txInfoFees > 0

    5. Minted value is valid, i.e,
         - validMintValue ctx.scriptContextTxInfo.txInfoMint

    6. Withdrawal list is sorted w.r.t. Credential
         - validWithdrawals ctx.scriptContextTxInfo.txInfoWdrl

    7. Validity range cannot be empty
        - ¬ isEmpty ctx.scriptContextTxInfo.txInfoValidRange

    8. List of signatories is sorted w.r.t. PubKeyHash
         - validSigners ctx.scriptContextTxInfo.txInfoSignatories

    9. RedeemerMap is sorted w.r.t. ScriptPurpose
         - validRedeemerMap ctx.scriptContextTxInfo.txInfoRedeemers

    10. DatumMap is sorted w.r.t.DatumHash
         - validDatumMap ctx.scriptContextTxInfo.txInfoData

    11. VoterMap is sorted w.r.t Voter with each inner Map sorted w.r.t. GovernanceActionId
          - validVoterMap ctx.scriptContextTxInfo.txInfoVotes

    12. treasury amount > 0, if any

    13. donation amount > 0, if any

    14. Transaction is balanced, i.e.,
        - Value in inputs + txInfoMint = Value in outputs + txInfoFees
-/
def validTxInfo (ctx : ScriptContext) : Bool :=
  validInputs ctx &&
  validReferenceInputs ctx &&
  validOutputs ctx.scriptContextTxInfo.txInfoOutputs &&
  ctx.scriptContextTxInfo.txInfoFee > 0 &&
  validMintValue ctx.scriptContextTxInfo.txInfoMint &&
  validWithdrawals ctx.scriptContextTxInfo.txInfoWdrl &&
  V2.validTxRange ctx.scriptContextTxInfo.txInfoValidRange &&
  V2.validSigners ctx.scriptContextTxInfo.txInfoSignatories &&
  validRedeemerMap ctx.scriptContextTxInfo.txInfoRedeemers &&
  V2.validDatumMap ctx.scriptContextTxInfo.txInfoData &&
  validVoterMap ctx.scriptContextTxInfo.txInfoVotes &&
  validTreasuryAmount ctx.scriptContextTxInfo.txInfoCurrentTreasuryAmount &&
  validTreasuryDonation ctx.scriptContextTxInfo.txInfoTreasuryDonation &&
  isBalanced ctx


/-- [LEDGER-RULE]: Ledger rules for ScriptContext (V3):
    A ScriptContext ctx is valid if and only if the following conditions are satisfied:
    1. ScriptInfo is valid, i.e.,
        - validScriptInfo ctx

    2. The pending transaction is valid, i.e.,
        - validTxInfo ctx

    with:
       - ctx : corresponding to the ScriptContext applied to the current validator script.
-/
def validScriptContext (ctx : ScriptContext) : Bool :=
  validScriptInfo ctx &&
  validTxInfo ctx


end CardanoLedgerApi.V3.Contexts
