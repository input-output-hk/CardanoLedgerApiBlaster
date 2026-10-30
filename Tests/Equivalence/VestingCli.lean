import Tests.Equivalence.Support

namespace Tests.Equivalence.VestingCli

open Support

set_option stderrAsMessages false

-- This normal CLI invocation previously failed while translating Nat.log2
-- because Lake selected the unpatched PlutusCoreBlaster dependency.
#eval show IO Unit from do
  let report ← runBounded { acceptanceConfig with
    scripts := #["equivalence/examples/linear_vesting/Plinth_1.45.0.0_Unisay.cbor_hex",
      "equivalence/examples/linear_vesting/Plinth_1.67.0.0_Unisay.cbor_hex"]
    inputs := "vesting-full", rawContext := false, budget := some (10000000, 1000000) }
  verdict report "vacuously_preserved"
  expect report ["queries", "old_rejected"] "valid"
  expect report ["ledger_validity", "valid"] true
  noCounterexample report

-- The first model-valid family is unsigned and rejected. At a sufficient
-- budget the accepting-witness search must continue to a signed full-unlock
-- case, rather than report inconclusive after checking only the first family.
#eval show IO Unit from do
  let report ← runBounded { acceptanceConfig with
    scripts := #["equivalence/examples/linear_vesting/Plinth_1.45.0.0_Unisay.cbor_hex",
      "equivalence/examples/linear_vesting/Plinth_1.67.0.0_Unisay.cbor_hex"]
    inputs := "vesting-full", rawContext := false, budget := some (1000000000, 1000000) }
  verdict report "preserved"
  expect report ["old_acceptance_witness", "old", "accepts"] true
  expect report ["old_acceptance_witness", "ledger_validity", "valid"] true
  noCounterexample report

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
