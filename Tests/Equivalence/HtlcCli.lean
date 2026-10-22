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
  config := { Support.config with language := "PlutusV3", steps := 100000 }
  modes := #["htlc-refund", "htlc-claim"]
  variationGroups := (_root_.Equivalence.HTLC.variationGroups.map List.toArray).toArray
  caseCount := _root_.Equivalence.HTLC.cases.size }

-- Known limit: secret-empty, case 3, has exceeded the 60-second worker deadline
-- in both modes for Plinth_1.67.0.0_Unisay_asdata vs Scalus_0.18.2_Unisay at
-- 100000 fuel. The deadline includes preprocessing and solving; the cause has
-- not been isolated. These checks remain inconclusive and fail the batch.
-- Reproduce after `lake build uplc_equiv` (bypassing Lake's test-module cache):
-- SEED=16156505056455167060 lake env lean --memory=8192 Tests/Equivalence/HtlcCli.lean
#eval runExploration scenario

end Tests.Equivalence.HtlcCli
