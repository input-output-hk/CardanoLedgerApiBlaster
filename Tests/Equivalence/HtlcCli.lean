import Tests.Equivalence.Support

namespace Tests.Equivalence.HtlcCli

open Support

set_option stderrAsMessages false

-- This pair used to exhaust the wall-clock limit during the two-script query.
-- Proving OLD rejects this entire domain settles the forward implication.
#eval show IO Unit from do
  let report ← runBounded { acceptanceConfig with
    scripts := #["equivalence/examples/htlc/Plinth_1.64.0.0_Unisay.cbor_hex",
      "equivalence/examples/htlc/Plinth_1.65.0.0_Unisay.cbor_hex"]
    inputs := "htlc-claim", caseIndex := some 45, variation := "hash-empty", rawContext := false }
  verdict report "vacuously_preserved"
  expect report ["domain_status"] "nonempty"
  expect report ["ledger_validity", "valid"] true
  expect report ["queries", "old_rejected"] "valid"
  expect report ["derived_queries", "acceptance_preserved"] "old_rejected"
  noCounterexample report

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
