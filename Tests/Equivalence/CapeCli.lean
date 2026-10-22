import Tests.Equivalence.Support

namespace Tests.Equivalence.CapeCli

open Support Lean

def script (scenario submission : String) : String :=
  s!"equivalence/examples/{scenario}/{submission}.cbor_hex"

#eval do
  for (scenario, left, right) in [
      ("factorial", "Scalus_0.12.1_Unisay", "Plutarch_1.11.0_SeungheonOh_exbudget"),
      ("factorial_naive_recursion", "Scalus_0.12.1_Unisay", "Scalus_0.16.0_Unisay"),
      ("fibonacci", "Scalus_0.12.1_Unisay", "Plutarch_1.11.0_SeungheonOh_size"),
      ("fibonacci_naive_recursion", "Scalus_0.12.1_Unisay", "Scalus_0.16.0_Unisay")] do
    let report ← _root_.Equivalence.Cli.run { config with scripts := #[script scenario left, script scenario right], steps := 100 }
    -- Require completed queries: exhaustion over the unrestricted integer domain
    -- is inconclusive, but shared completed outputs must agree non-vacuously.
    verdict report "inconclusive"
    expect report ["queries"] (Json.mkObj [
      ("shared_integer_outputs", toJson "valid"), ("no_completed_mismatch", toJson "valid"),
      ("total_equivalence", toJson "falsified"), ("left_sometimes_output", toJson "valid"),
      ("right_sometimes_output", toJson "valid")])
    noCounterexample report

#eval do
  let report ← _root_.Equivalence.Cli.run { config with steps := 100, scripts := #[
    script "factorial" "Scalus_0.12.1_Unisay", script "fibonacci" "Scalus_0.12.1_Unisay"] }
  verdict report "inequivalent"
  let w ← witness report
  discard <| IO.ofExcept ((← field w ["input"]).getInt?)
  expect w ["left", "kind"] "integer"
  expect w ["right", "kind"] "integer"
  check report ((← field w ["left", "value"]) != (← field w ["right", "value"]))
    "Factorial and Fibonacci returned the same value"

end Tests.Equivalence.CapeCli
