import CardanoLedgerApi.V2
import CardanoLedgerApi.V3.Contexts
import CardanoLedgerApi.V3.Tx
import CardanoLedgerApi.V3.TxCert
import CardanoLedgerApi.V3.Governance

namespace CardanoLedgerApi.V3
  export V2 (
    -- Addresses
    Address
    hasPubKeyHash
    hasScriptHash
    isPubKeyCredentialAddress
    isScriptCredentialAddress
    toPubKeyHash
    toScriptHash
    -- Credentials
    Credential
    PubKeyHash
    StakingCredential
    hasScriptCredential
    hasPubKeyCredential
    isScriptCredential
    isPubKeyCredential
    isStakingScriptCredential
    -- Script Context
    DatumMap
    findDatum
    findDatumHash
    findOutput
    findPubKeyOutputs
    findScriptOutputs
    validDatumMap
    validSigners
    validScriptCertificate
    validWithdrawals
    validTxRange
    validTxOutValue
    validMintValue
    -- Scripts
    Datum
    Redeemer
    ScriptHash
    DatumHash
    -- Time
    Closure
    InfiniteBound
    LowerBound
    UpperBound
    POSIXTime
    POSIXTimeRange
    everything
    empty
    strictUpperBound
    strictLowerBound
    lowerBound
    upperBound
    after
    entirelyAfter
    before
    entirelyBefore
    between
    entirelyBetween
    hull
    intersection
    isEmpty
    includes
    contains
    isEntirelyAfter
    isEntirelyBefore
    -- Tx
    OutputDatum
    TxOut
    txOutPubKey
    txOutScriptHash
    txOutInlineDatum
    txOutDatumHash
    hasScriptAddress
    hasPubKeyAddress
    hasDatum
    hasDatumHash
    hasReferenceScript
    -- Value
    CurrencySymbol
    TokenName
    Value
    adaSymbol
    adaToken
    null
    lovelaceValue
    singleton
    onlyLovelace
    withoutLovelace
    lovelaceOf
    valueOf
    add
    merge
    hasCurrencySymbol
    hasOnlyCurrencySymbol
    hasOnlyNonZeroAda
  )
  -- V3 Governance
  export Governance (
    GovernanceActionId
    ProposalProcedure
    Vote
    Voter
  )
  -- V3.Tx
  export Tx (
    TxId
    TxOutRef
  )
  -- V3 Certificates
  export TxCert (
    DRep
    Delegatee
    TxCert
    isRegisterStakingCertificate
    isUnRegisterStakingCertificate
    isDelegationStakingCertficate
    isRegisterAndDelegationCertficate
  )
  -- V3 ScriptContext
  export Contexts (
    GovernanceVoteMap
    MintValue
    RedeemerMap
    ScriptContext
    ScriptPurpose
    ScriptInfo
    TxInfo
    TxInInfo
    VoterMap
    Withdrawals
    resolveInput
    findOwnInput
    findPubKeyInputs
    findScriptInputs
    findInput
    findRedeemer
    ownCurrencySymbol
    valueSpent
    valueProduced
    spendingInputs
    mintingInputs
    rewardingInputs
    certifyingInputs
    votingInputs
    proposingInputs
    isMintingScriptInfo
    isRewardingScriptInfo
    isSpendingScriptInfo
    isCertifyingScriptInfo
    isVotingScriptInfo
    isProposingScriptInfo
    utxoConsumed
    txSignedBy
    onlySingedBy
    credentialInWithdrawals
    isKnownCertificate
    isKnownProposal
    isKnownVoter
    validMintValue
    validInputDatum
    validScriptCertificate
    validScriptVoter
    validScriptProposal
    validScriptInfo
    validInputs
    validReferenceInputs
    validOutputs
    validWithdrawals
    validRedeemerMap
    validGovernanceVoteMap
    validVoterMap
    validTreasuryAmount
    validTreasuryDonation
    isBalanced
    validTxInfo
    validScriptContext
  )

end CardanoLedgerApi.V3
