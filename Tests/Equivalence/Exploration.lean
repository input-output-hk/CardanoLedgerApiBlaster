import Tests.Equivalence.Support

namespace Tests.Equivalence.Exploration

open Support

set_option stderrAsMessages false

-- Distinct closed programs returning closures without inspecting their input.
-- Both finish successfully; zero fuel makes every comparison inconclusive.
-- Exercise the actual sampler and Lean workers across all contract input modes.
#eval show IO Unit from IO.FS.withTempDir fun directory => do
  IO.FS.writeFile (directory / "left.cbor_hex") "480100002221200101"
  IO.FS.writeFile (directory / "right.cbor_hex") "480100002221200201"
  let modes := #["htlc-refund", "htlc-claim", "vesting-full", "vesting-partial",
    "escrow-refund", "escrow-accept", "escrow-deposit"]
  let scenario : Support.Exploration := {
    label := "SharedRunner"
    directory
    legacySeed := "EXPLORATION_SEED"
    config
    modes
    variationGroups := #[_root_.Equivalence.Context.baselineGroup.toArray, _root_.Equivalence.Context.feeGroup.toArray]
    caseCount := 1 }
  runExploration scenario
  let failure ← try
    runExploration { scenario with config := { config with steps := 0 } }
    pure ""
  catch error => pure error.toString
  unless (failure.splitOn "Inconclusive SharedRunner checks:").length == 2 do
    throw <| IO.userError s!"Expected an inconclusive batch failure, got: {failure}"
  for mode in modes do
    unless (failure.splitOn s!"{mode}, case 0, variation").length == 3 do
      throw <| IO.userError s!"Runner skipped a remaining group for {mode}: {failure}"

end Tests.Equivalence.Exploration
