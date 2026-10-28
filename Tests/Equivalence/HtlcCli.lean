import Tests.Equivalence.Support

namespace Tests.Equivalence.HtlcCli

open Support

set_option stderrAsMessages false

/-- Random distinct submissions, boundary cases and context variations.
    Set SEED to reproduce the complete exploration. -/
def scenario : Exploration := {
  label := "HTLC"
  directory := "equivalence/examples/htlc"
  legacySeed := "HTLC_SEED"
  config := acceptanceConfig
  modes := #["htlc-refund", "htlc-claim"]
  variationGroups := (_root_.Equivalence.HTLC.variationGroups.map List.toArray).toArray
  caseCount := _root_.Equivalence.HTLC.cases.size }

-- Timeouts remain inconclusive and fail the batch; empty secrets are not skipped.
#eval runExploration scenario

end Tests.Equivalence.HtlcCli
