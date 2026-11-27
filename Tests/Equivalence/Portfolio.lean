import Tests.Equivalence.Support

namespace Tests.Equivalence.Portfolio
open Support Lean

-- Portfolio models must retain the structured ledger bindings needed for
-- native replay, including negative and large integers in the reverse direction.
#eval do
  for n in ([-42, 987654321012345678901234567890] : List Int) do
    let old := rejectIf s!"[[(builtin equalsData) {datumTerm}] (con data (I {n}))]"
    let report ← comparePrograms old "(lam n (con unit ()))" { config with solverJobs := 2 }
    verdict report "inequivalent"
    expect report ["solver_workers"] (2 : Nat)
    let w ← witness report
    expect (← dataField (← field w ["input"]) [2, 1, 0]) ["int"] n
    expect w ["direction"] "new_to_old"

end Tests.Equivalence.Portfolio
