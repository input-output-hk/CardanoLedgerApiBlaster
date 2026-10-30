import Tests.Equivalence.Support

namespace Tests.Equivalence.Function
open Support Lean
open _root_.Equivalence.Cli (parse)

def settings : _root_.Equivalence.Cli.Config := {
  mode := "function", inputs := "integer", timeout := 5, wallTimeout := 8 }

-- Specialized CEK Data lists and pairs denote the same UPLC constants.
#eval show IO Unit from do
  let success := fun value => _root_.Equivalence.Acceptance.Result.success
    (.VCon value) ⟨⟨0⟩, ⟨0⟩⟩
  for (a, b) in [
      (.ConstDataList [.I 1], .ConstList [.Data (.I 1)]),
      (.PairData (.I 1, .I 2), .Pair (.Data (.I 1), .Data (.I 2))),
      (.ConstPairDataList [(.I 1, .I 2)], .ConstList [.Pair (.Data (.I 1), .Data (.I 2))]),
      (.ConstList [.ConstDataList [.I 1]], .ConstList [.ConstList [.Data (.I 1)]])] do
    unless _root_.Equivalence.Function.same (success a) (success b) == some true do
      throw <| IO.userError "Equivalent constant representations differ"

-- Defaults and explicit overrides are independent of option order.
#eval show IO Unit from do
  let paths := ["old.uplc", "new.uplc"]
  let c ← IO.ofExcept (parse {} (paths ++ ["--mode", "function"]))
  unless c.mode == "function" && c.inputs == "integer" && c.budget.isNone &&
      c.language == "PlutusV3" && c.leftFormat == some "textual" && c.rightFormat == some "textual" do
    throw <| IO.userError "Unexpected function defaults"
  unless _root_.Equivalence.Cli.queryNames c == #["function_equivalent"] do
    throw <| IO.userError "Function mode must only compare outcomes"
  for options in [["--inputs", "data", "--mode", "function"],
      ["--mode", "function", "--inputs", "data"]] do
    let c ← IO.ofExcept (parse {} (paths ++ options))
    unless c.inputs == "data" do throw <| IO.userError "Explicit input mode lost"
  let c ← IO.ofExcept (parse {} (paths ++ ["--mode", "validator", "--budget", "1000000", "10000"]))
  unless c.inputs == "valid-context" && c.mode == "validator" do
    throw <| IO.userError "Validator defaults changed"
  for options in [[], ["--mode", "bogus"], ["--mode", "function", "--inputs", "valid-context"],
      ["--mode", "function", "--equivalence"], ["--mode", "function", "--skip-old-rejected"],
      ["--mode", "function", "--steps", "0"]] do
    unless (parse {} (paths ++ options) matches .error _) do
      throw <| IO.userError s!"Expected invalid options: {options}"
  let explicit ← IO.ofExcept (parse {} (paths ++ ["--mode", "function", "--format", "flat_hex"]))
  unless explicit.leftFormat.isNone && explicit.format == "flat_hex" do
    throw <| IO.userError "Explicit format lost"

-- A real optimizer bug: strict evaluation of an unused argument divides by zero.
-- No V2, budget, equivalence, input-type or rejection-query switches are needed.
#eval show IO Unit from do
  let c ← IO.ofExcept (parse {} ["equivalence/examples/uplc-optimize/ifthenelse.uplc",
    "equivalence/examples/uplc-optimize/ifthenelseopt.uplc", "--mode", "function"])
  let r ← runBounded { c with timeout := 5, wallTimeout := 8 }
  verdict r "inequivalent"
  expect r ["mode"] "function"
  let w ← witness r
  expect w ["input"] (0 : Int)
  expect w ["old", "kind"] "error"
  expect w ["new", "result", "value"] (1 : Int)

-- Value differences matter even when both evaluations succeed under V3.
#eval show IO Unit from do
  let r ← comparePrograms "(lam n (con integer 1))" "(lam n (con integer 2))" settings
  verdict r "inequivalent"
  let w ← witness r
  expect w ["old", "result", "value"] (1 : Int)
  expect w ["new", "result", "value"] (2 : Int)
  let r ← comparePrograms "(lam n n)" "(lam n [[(builtin addInteger) n] (con integer 0)])" settings
  verdict r "equivalent"
  noCounterexample r
  let r ← comparePrograms "(lam n (error))" "(lam n (error))" settings
  verdict r "equivalent"

-- Input-dependent differences must replay the solver's input, not just zero.
#eval show IO Unit from do
  let old := "(lam c (force [[[(force (builtin ifThenElse)) " ++
    "[[(builtin equalsInteger) c] (con integer 42)]] (delay (con integer 2))] (delay (con integer 1))]))"
  let r ← comparePrograms old "(lam n (con integer 1))" settings
  verdict r "inequivalent"
  expect (← witness r) ["input"] (42 : Int)
  for inputs in ["data", "data3"] do
    let body := if inputs == "data" then "(lam n (con integer 1))"
      else "(lam d (lam r (lam c (con integer 1))))"
    verdict (← comparePrograms body body { settings with inputs }) "equivalent"
  let r ← comparePrograms "(lam n (con integer 1))" "(lam n (con integer 2))"
    { settings with inputs := "data" }
  verdict r "inequivalent"
  let w ← witness r
  unless (w.getObjVal? "ledger_validity").toOption.isNone do
    throw <| IO.userError "Function inputs must not be audited as ledger contexts"

-- Hitting either limit or returning a closure cannot establish equivalence.
#eval show IO Unit from do
  for c in [{ settings with steps := 1 }, { settings with budget := some (1, 1) }] do
    let r ← comparePrograms "(lam n (con integer 1))"
      "(lam n [[(builtin addInteger) (con integer 0)] (con integer 1)])" c
    verdict r "inconclusive"
    noCounterexample r
  let r ← comparePrograms "(lam n (lam x x))"
    "(lam n (lam x [[(builtin addInteger) x] (con integer 0)]))" settings
  verdict r "inconclusive"
  noCounterexample r
  let r ← comparePrograms "(lam n (con integer 1))"
    "(lam n [[(builtin addInteger) (con integer 0)] (con integer 1)])"
    { settings with budget := some (1000000, 10000) }
  verdict r "equivalent"

-- These compiler submissions contain the same decoded program. Identity proves
-- equivalence even where bounded evaluation cannot prove universal completion.
#eval show IO Unit from do
  for c in [settings, { settings with steps := 1, budget := some (1, 1) }] do
    let r ← runBounded { c with
      wallTimeout := 3
      scripts := #["equivalence/examples/factorial/Plutarch_1.11.0_SeungheonOh_size.cbor_hex",
        "equivalence/examples/factorial/Scalus_0.17.0_Unisay.cbor_hex"] }
    verdict r "equivalent"
    expect r ["queries", "program_identity"] "valid"
    expect r ["derived_queries", "function_equivalent"] "program_identity"
    expect r ["verification"] "Decoded UPLC program equality; no SMT query required"
    noCounterexample r
  -- Identity concerns decoded terms, including de Bruijn binders, not file bytes.
  let r ← comparePrograms "(lam n n)" "(lam renamed renamed)" settings
  verdict r "equivalent"
  expect r ["queries", "program_identity"] "valid"
  -- This establishes identical behavior, without claiming termination.
  let omega := "(lam n [(lam x [x x]) (lam x [x x])])"
  let r ← comparePrograms omega omega { settings with steps := 1 }
  verdict r "equivalent"
  expect r ["queries", "program_identity"] "valid"

-- Bounded checks deliberately equate absent observations, including errors and
-- analysis exhaustion. Strict checks retain their inconclusive result.
#eval show IO Unit from do
  let left := "(lam n (con integer 1))"
  let right := "(lam n (con integer 2))"
  let strict ← comparePrograms left right { settings with steps := 1 }
  verdict strict "inconclusive"
  let bounded ← comparePrograms left right { settings with bounded := true, steps := 1 }
  verdict bounded "bounded_preserved"
  expect bounded ["function_check"] "bounded_preservation"
  expect bounded ["queries", "bounded_function_preserved"] "valid"
  unless _root_.Equivalence.Cli.exitCode bounded == 0 do
    throw <| IO.userError "Bounded equality should exit 0"
  let mismatch ← comparePrograms left right { settings with bounded := true }
  verdict mismatch "bounded_regression"
  let w ← witness mismatch
  expect w ["old", "result", "value"] (1 : Int)
  expect w ["new", "result", "value"] (2 : Int)
  unless _root_.Equivalence.Cli.exitCode mismatch == 1 do
    throw <| IO.userError "Bounded difference should exit 1"
  let errorVsLimit ← comparePrograms "(lam n (error))"
    "(lam n [(lam x [x x]) (lam x [x x])])"
    { settings with bounded := true, steps := 10 }
  verdict errorVsLimit "bounded_preserved"
  let completedVsLimit ← comparePrograms left
    "(lam n [(lam x [x x]) (lam x [x x])])"
    { settings with bounded := true, steps := 10 }
  verdict completedVsLimit "bounded_regression"
  expect (← witness completedVsLimit) ["new", "kind"] "unfinished"
  let budget ← comparePrograms left right { settings with bounded := true, budget := some (1, 1) }
  verdict budget "bounded_preserved"
  for inputs in ["data", "data3"] do
    let left := if inputs == "data" then "(lam n (con integer 1))"
      else "(lam d (lam r (lam c (con integer 1))))"
    let right := if inputs == "data" then "(lam n (con integer 2))"
      else "(lam d (lam r (lam c (con integer 2))))"
    verdict (← comparePrograms left right { settings with inputs, bounded := true, steps := 1 })
      "bounded_preserved"
  let validator ← IO.ofExcept (parse {} ["old", "new", "--bounded", "--budget", "1", "1"])
  unless validator.mode == "validator" && validator.bounded do
    throw <| IO.userError "Bounded validator mode was not selected"

-- The real Fibonacci implementations agree on their 1000-step observations.
-- Successful concrete runs rule out an entirely empty observation domain.
#eval show IO Unit from do
  let paths := #["Tests/Functions/Fibonacci/fibonacci_naive.flat",
    "Tests/Functions/Fibonacci/fibonacci_size.flat"]
  let c := { settings with
    scripts := paths
    bounded := true
    steps := 1000
    language := "PlutusV2"
    wallTimeout := 8 }
  let r ← runBounded c
  verdict r "bounded_preserved"
  expect r ["steps"] (1000 : Nat)
  expect r ["queries", "bounded_function_preserved"] "valid"
  for path in paths do
    let program ← _root_.Equivalence.Cli.readProgram path "single_cbor_hex"
    for n in ([0, 1, 5] : List Int) do
      let result := _root_.Equivalence.Function.execute program
        (_root_.Equivalence.Queries.args n) 0 0 false false 1000
      unless _root_.Equivalence.Function.observation result == some (.Integer n) do
        throw <| IO.userError s!"Expected Fibonacci({n}) = {n}: {reprStr result}"
    let exhausted := _root_.Equivalence.Function.execute program
      (_root_.Equivalence.Queries.args 20) 0 0 false false 1000
    unless exhausted matches .unfinished do
      throw <| IO.userError "Expected Fibonacci(20) to exhaust the analysis limit"

-- Additional NEW results are allowed by --bounded, and rejected when checking
-- both directions. Losing an OLD result fails either check.
#eval show IO Unit from do
  let value := "(lam n (con integer 1))"
  let loop := "(lam n [(lam x [x x]) (lam x [x x])])"
  let slowValue := "(lam n [[(builtin addInteger) (con integer 0)] (con integer 1)])"
  for (old, c, exhaustedKind) in [
      (loop, { settings with bounded := true, steps := 10 }, "unfinished"),
      (slowValue, { settings with bounded := true, budget := some (100000, 10000) }, "budget_exhausted")] do
    let forward ← comparePrograms old value c
    verdict forward "bounded_preserved"
    expect forward ["queries", "bounded_function_preserved"] "valid"
    let symmetric ← comparePrograms old value { c with equivalence := true }
    verdict symmetric "bounded_inequivalent"
    expect symmetric ["queries", "bounded_function_equivalent"] "falsified"
    let w ← witness symmetric
    expect w ["old", "kind"] exhaustedKind
    expect w ["new", "result", "value"] (1 : Int)
    let reverse ← comparePrograms value old c
    verdict reverse "bounded_regression"
    let w ← witness reverse
    expect w ["old", "result", "value"] (1 : Int)
    expect w ["new", "kind"] exhaustedKind
  for options in [["--bounded", "--equivalence"], ["--equivalence", "--bounded"]] do
    let c ← IO.ofExcept (parse {} (["old", "new", "--mode", "function"] ++ options))
    unless c.bounded && c.equivalence do throw <| IO.userError "Bounded equivalence flags lost"
  let mismatch ← comparePrograms value "(lam n (con integer 2))"
    { settings with bounded := true, equivalence := true }
  verdict mismatch "bounded_inequivalent"
  let identity ← comparePrograms value value { settings with bounded := true, equivalence := true }
  verdict identity "bounded_equivalent"
  expect identity ["queries", "program_identity"] "valid"
  for inputs in ["data", "data3"] do
    let wrap := fun body => if inputs == "data" then s!"(lam n {body})"
      else s!"(lam d (lam r (lam c {body})))"
    let old := wrap "(error)"
    let new := wrap "(con integer 1)"
    verdict (← comparePrograms old new { settings with inputs, bounded := true }) "bounded_preserved"
    verdict (← comparePrograms old new { settings with inputs, bounded := true, equivalence := true })
      "bounded_inequivalent"

end Tests.Equivalence.Function
