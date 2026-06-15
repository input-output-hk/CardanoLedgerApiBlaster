import CardanoLedgerApi.IsData.Class
import CardanoLedgerApi.V3
import Tests.Scripts.Governance.Governance
import Blaster

namespace Tests.Scripts.Governance
open CardanoLedgerApi.IsData.Class
open CardanoLedgerApi.V3
open PlutusCore.UPLC.Utils
open PlutusCore.Integer (Integer)
open PlutusCore.Data (Data)

set_option warn.sorry false

def minFeeAId : Integer := 0
def minFeeBId : Integer := 1
def maxBodyBlockSizeId : Integer := 2
def maxTxSizeId : Integer := 3
def maxBlockHeaderSizeId : Integer := 4
def stakeAddressDepositId : Integer := 5
def stakePoolDepositId : Integer := 6
def poolRetireMaxEpochId : Integer := 7
def stakePoolTargetNumId : Integer := 8

def hasParamProposalWithValue (ctx : ScriptContext) (idx : Integer) (v : Integer) : Bool :=
  match (ownChangeParameters ctx) with
  | some pupdates => Recursor.any x in pupdates => x.1 == Data.I idx && x.2 == Data.I v
  | _ => false

def hasParamProposal (ctx : ScriptContext) (idx : Integer) : Bool :=
  match (ownChangeParameters ctx) with
  | some pupdates => Recursor.any x in pupdates => x.1 == Data.I idx
  | _ => false

def hasTreasuryWithdrawalsProposal (ctx : ScriptContext) : Bool :=
  match ctx.scriptContextScriptInfo with
  | .ProposingScript _idx proposal =>
          match (IsData.fromData proposal.ppGovernanceAction : Option GovernanceAction) with
          | some (.TreasuryWithdrawals ..) => true
          | _ => false
  | _ => false

def isUnknownParam (id : Integer) : Prop := id < 0 ∨ id > 33 ∨ (id ≥ 12 ∧ id ≤ 15)

/-- Governance script is always successful for treasuryWithdrawals proposal . -/
theorem governance_successful_for_treasury_withdrawals :
  ∀ (ctx : ScriptContext),
    validProposingContext ctx →
    hasTreasuryWithdrawalsProposal ctx →
    isSuccessful (appliedGovernance.prop ctx) := by blaster

/-- Governance script is not successful for unknown parameters . -/
theorem governance_unsuccessful_for_unknown_param :
  ∀ (ctx : ScriptContext) (paramKey : Integer),
    validProposingContext ctx →
    isUnknownParam paramKey →
    hasParamProposal ctx paramKey →
    ¬ isSuccessful (appliedGovernance.prop ctx) := by blaster

/-- Governance script successful for a minFeeA change proposal → minFeeA ≥ 30 ∧ minFeeA ≤ 1_000 -/
theorem valid_minFeeA_changed :
  ∀ (ctx : ScriptContext) (value : Integer),
    validProposingContext ctx →
    isSuccessful (appliedGovernance.prop ctx) →
    hasParamProposalWithValue ctx minFeeAId value →
    value ≥ 30 ∧ value ≤ 1_000 := by blaster

/-- Governance script is not successful for a minFeeA change proposal when minFeeA < 30 ∨ minFeeA > 1_000 -/
theorem invalid_minFeeA_changed :
  ∀ (ctx : ScriptContext) (value : Integer),
    validProposingContext ctx →
    hasParamProposalWithValue ctx minFeeAId value →
    ( value < 30 ∨ value > 1_000 ) →
    ¬ isSuccessful (appliedGovernance.prop ctx) := by blaster

/-- Governance script successful for a minFeeB change proposal → minFeeB ≥ 100_000 ∧ minFeeB ≤ 10_000_000 -/
theorem valid_minFeeB_changed :
  ∀ (ctx : ScriptContext) (value : Integer),
    validProposingContext ctx →
    isSuccessful (appliedGovernance.prop ctx) →
    hasParamProposalWithValue ctx minFeeBId value →
    value ≥ 100_000 ∧ value ≤ 10_000_000 := by blaster

/-- Governance script is not successful for a minFeeB change proposal when minFeeB < 100_000 ∨ minFeeB > 10_000_000 -/
theorem invalid_minFeeB_changed :
  ∀ (ctx : ScriptContext) (value : Integer),
    validProposingContext ctx →
    hasParamProposalWithValue ctx minFeeBId value →
    ( value < 100_000 ∨ value > 10_000_000 ) →
    ¬ isSuccessful (appliedGovernance.prop ctx) := by blaster

/-- Governance script successful for a maxBodyBlockSize change proposal →
    maxBodyBlockSize ≥ 24_576 ∧ maxBodyBlockSize ≤ 122_880
-/
theorem valid_maxBodyBlockSize_changed :
  ∀ (ctx : ScriptContext) (value : Integer),
    validProposingContext ctx →
    isSuccessful (appliedGovernance.prop ctx) →
    hasParamProposalWithValue ctx maxBodyBlockSizeId value →
    value ≥ 24_576 ∧ value ≤ 122_880 := by blaster

/-- Governance script is not successful for a maxBodyBlockSize change proposal when
    maxBodyBlockSize < 24_576 ∨ maxBodyBlockSize > 122_880
-/
theorem invalid_maxBodyBlockSize_changed :
  ∀ (ctx : ScriptContext) (value : Integer),
    validProposingContext ctx →
    hasParamProposalWithValue ctx maxBodyBlockSizeId value →
    ( value < 24_576 ∨ value > 122_880 ) →
    ¬ isSuccessful (appliedGovernance.prop ctx) := by blaster


/-- Governance script successful for a maxTxSize change proposal → maxTxSize ≥ 0 ∧ maxTxSize ≤ 32_768 -/
theorem valid_maxTxSize_changed :
  ∀ (ctx : ScriptContext) (value : Integer),
    validProposingContext ctx →
    isSuccessful (appliedGovernance.prop ctx) →
    hasParamProposalWithValue ctx maxTxSizeId value →
    value ≥ 0 ∧ value ≤ 32_768 := by blaster

/-- Governance script is not successful for a maxTxSize change proposal when maxTxSize < 0 ∨ maxTxSize > 32_768 -/
theorem invalid_maxTxSize_changed :
  ∀ (ctx : ScriptContext) (value : Integer),
    validProposingContext ctx →
    hasParamProposalWithValue ctx maxTxSizeId value →
    ( value < 0 ∨ value > 32_768 ) →
    ¬ isSuccessful (appliedGovernance.prop ctx) := by blaster

/-- Governance script successful for a maxBlockHeaderSize change proposal →
    maxBlockHeaderSize ≥ 0 ∧ maxBlockHeaderSize ≤ 5_000
-/
theorem valid_maxBlockHeaderSize_changed :
  ∀ (ctx : ScriptContext) (value : Integer),
    validProposingContext ctx →
    isSuccessful (appliedGovernance.prop ctx) →
    hasParamProposalWithValue ctx maxBlockHeaderSizeId value →
    value ≥ 0 ∧ value ≤ 5_000 := by blaster

/-- Governance script is not successful for a maxBlockHeaderSize change proposal when
    maxBlockHeaderSize < 0 ∨ maxBlockHeaderSize > 5_000
-/
theorem invalid_maxBlockHeaderSize_changed :
  ∀ (ctx : ScriptContext) (value : Integer),
    validProposingContext ctx →
    hasParamProposalWithValue ctx maxBlockHeaderSizeId value →
    value < 0 ∨ value > 5_000 →
    ¬ isSuccessful (appliedGovernance.prop ctx) := by blaster

/-- Governance script successful for a stakeAddressDeposit change proposal →
    stakeAddressDeposit ≥ 1_000_000 ∧ stakeAddressDeposit ≤ 5_000_000
-/
theorem valid_stakeAddressDeposit_changed :
  ∀ (ctx : ScriptContext) (value : Integer),
    validProposingContext ctx →
    isSuccessful (appliedGovernance.prop ctx) →
    hasParamProposalWithValue ctx stakeAddressDepositId value →
    value ≥ 1_000_000 ∧ value ≤ 5_000_000 := by blaster

/-- Governance script is not successful for a stakeAddressDeposit change proposal when
    stakeAddressDeposit < 1_000_000 ∨ stakeAddressDeposit > 5_000_000
-/
theorem invalid_stakeAddressDeposit_changed :
  ∀ (ctx : ScriptContext) (value : Integer),
    validProposingContext ctx →
    hasParamProposalWithValue ctx stakeAddressDepositId value →
    ( value < 1_000_000 ∨ value > 5_000_000 ) →
    ¬ isSuccessful (appliedGovernance.prop ctx) := by blaster


/-- Governance script successful for a stakePoolDeposit change proposal →
    stakePoolDeposit ≥ 250_000_000 ∧ stakePoolDeposit ≤ 500_000_000
-/
theorem valid_stakePoolDeposit_changed :
  ∀ (ctx : ScriptContext) (value : Integer),
    validProposingContext ctx →
    isSuccessful (appliedGovernance.prop ctx) →
    hasParamProposalWithValue ctx stakePoolDepositId value →
    value ≥ 250_000_000 ∧ value ≤ 500_000_000 := by blaster

/-- Governance script is not successful for a stakePoolDeposit change proposal when
    stakePoolDeposit < 250_000_000 ∨ stakePoolDeposit > 500_000_000
-/
theorem invalid_stakePoolDeposit_changed :
  ∀ (ctx : ScriptContext) (value : Integer),
    validProposingContext ctx →
    hasParamProposalWithValue ctx stakePoolDepositId value →
    ( value < 250_000_000 ∨ value > 500_000_000 ) →
    ¬ isSuccessful (appliedGovernance.prop ctx) := by blaster


/-- Governance script successful for a poolRetireMaxEpoch change proposal → poolRetireMaxEpoch ≥ 0 -/
theorem valid_poolRetireMaxEpoch_changed :
  ∀ (ctx : ScriptContext) (value : Integer),
    validProposingContext ctx →
    isSuccessful (appliedGovernance.prop ctx) →
    hasParamProposalWithValue ctx poolRetireMaxEpochId value →
    value ≥ 0 := by blaster

/-- Governance script is not successful for a poolRetireMaxEpoch change proposal when poolRetireMaxEpoch < 0 -/
theorem invalid_poolRetireMaxEpoch_changed :
  ∀ (ctx : ScriptContext) (value : Integer),
    validProposingContext ctx →
    hasParamProposalWithValue ctx poolRetireMaxEpochId value →
    value < 0 →
    ¬ isSuccessful (appliedGovernance.prop ctx) := by blaster


/-- Governance script successful for a stakePoolTargetNum change proposal →
    stakePoolTargetNum ≥ 250 ∧ stakePoolTargetNum ≤ 2_000
-/
theorem valid_stakePoolTargetNum_changed :
  ∀ (ctx : ScriptContext) (value : Integer),
    validProposingContext ctx →
    isSuccessful (appliedGovernance.prop ctx) →
    hasParamProposalWithValue ctx stakePoolTargetNumId value →
    value ≥ 250 ∧ value ≤ 2_000 := by blaster

/-- Governance script is not successful for a stakePoolTargetNum change proposal when
    stakePoolTargetNum < 250 ∨ stakePoolTargetNum > 2_000
-/
theorem invalid_stakePoolTargetNum_changed :
  ∀ (ctx : ScriptContext) (value : Integer),
    validProposingContext ctx →
    hasParamProposalWithValue ctx stakePoolTargetNumId value →
    value < 250 ∨ value > 2_000 →
    ¬ isSuccessful (appliedGovernance.prop ctx) := by blaster

end Tests.Scripts.Governance
