import Tests.Equivalence.Support

namespace Tests.Equivalence.EscrowCli

open Support

set_option stderrAsMessages false

/-- Random distinct decoded submissions, one sampled boundary case and one
    variation per group, across all three operations. Set SEED to reproduce.
    No fixed script pairs or fixed-comparison regressions are run here. -/
def scenario : Exploration := {
  label := "Escrow"
  directory := "equivalence/examples/two_party_escrow"
  legacySeed := "ESCROW_SEED"
  config := { Support.config with language := "PlutusV3", steps := 100000 }
  modes := #["escrow-refund", "escrow-accept", "escrow-deposit"]
  variationGroups := (_root_.Equivalence.Escrow.variationGroups.map List.toArray).toArray
  caseCount := _root_.Equivalence.Escrow.cases.size }

#eval runExploration scenario

end Tests.Equivalence.EscrowCli
