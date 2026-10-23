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

-- Historical step-based equivalence limit: secret-empty, case 3, exceeded the
-- 60-second worker deadline in both modes for Plinth_1.67.0.0_Unisay_asdata vs
-- Scalus_0.18.2_Unisay at 100000 fuel (SEED=16156505056455167060). The deadline
-- includes preprocessing and solving; the cause has not been isolated.
-- The budgeted direction also timed out for secret-empty, case 14, in both
-- modes: Plinth_1.64.0.0_Unisay_asdata → Scalus_0.17.0_Unisay, shared budget
-- CPU 10000000000 / memory 14000000. Reproduce the random exploration with:
-- SEED=5276846066013148466 lake env lean --memory=8192 Tests/Equivalence/HtlcCli.lean
-- Timeouts remain inconclusive and fail the batch; empty secrets are not skipped.
#eval runExploration scenario

end Tests.Equivalence.HtlcCli
