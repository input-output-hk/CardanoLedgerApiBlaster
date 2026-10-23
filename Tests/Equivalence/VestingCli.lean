import Tests.Equivalence.Support

namespace Tests.Equivalence.VestingCli

open Support

set_option stderrAsMessages false

/-- Random distinct submissions, boundary cases and context variations.
    Set SEED to reproduce the complete exploration. -/
def scenario : Exploration := {
  label := "Vesting"
  directory := "equivalence/examples/linear_vesting"
  legacySeed := "VESTING_SEED"
  config := acceptanceConfig
  modes := #["vesting-full", "vesting-partial"]
  variationGroups := (_root_.Equivalence.Vesting.variationGroups.map List.toArray).toArray
  caseCount := (_root_.Equivalence.Vesting.cases true).size
  caseForMode := fun mode index => if mode == "vesting-full" then index / 4 else index }

#eval runExploration scenario

end Tests.Equivalence.VestingCli
