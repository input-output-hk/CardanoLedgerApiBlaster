import Tests.Equivalence.Support

namespace Tests.Equivalence.Cli

open Support Lean

#eval do
  let report ← comparePrograms
    "(lam n [[(builtin addInteger) [[(builtin addInteger) n] (con integer 1)]] (con integer 1)])"
    "(lam n [[(builtin addInteger) n] (con integer 2)])"
  verdict report "equivalent"
  for name in ["total_equivalence", "left_sometimes_output", "right_sometimes_output"] do
    expect report ["queries", name] "valid"
  noCounterexample report

#eval do
  let report ← comparePrograms
    "(lam n [[(builtin addInteger) n] (con integer 1)])"
    "(lam n [[(builtin addInteger) n] (con integer 2)])"
  verdict report "inequivalent"
  expect report ["queries", "no_completed_mismatch"] "falsified"
  let w ← witness report
  let n ← IO.ofExcept ((← field w ["input"]).getInt?)
  expect w ["left"] (Json.mkObj [("kind", toJson "integer"), ("value", toJson (n + 1))])
  expect w ["right"] (Json.mkObj [("kind", toJson "integer"), ("value", toJson (n + 2))])

-- Neither witness can be found by always replaying the default input zero.
#eval do
  for n in ([-42, 987654321012345678901234567890] : List Int) do
    let report ← comparePrograms
      ("(lam n (force [[[(force (builtin ifThenElse)) " ++
        s!"[[(builtin equalsInteger) n] (con integer {n})]] " ++
        "(delay (con integer 1))] (delay (con integer 0))]))")
      "(lam n (con integer 0))" { config with steps := 100 }
    verdict report "inequivalent"
    let w ← witness report
    expect w ["input"] n
    expect w ["left"] (Json.mkObj [("kind", toJson "integer"), ("value", toJson (1 : Int))])
    expect w ["right"] (Json.mkObj [("kind", toJson "integer"), ("value", toJson (0 : Int))])

#eval do
  let report ← comparePrograms "(lam n n)" "(lam n n)" { config with steps := 0 }
  verdict report "inconclusive"
  expect report ["queries", "shared_integer_outputs"] "valid"
  expect report ["queries", "left_sometimes_output"] "falsified"
  noCounterexample report

#eval do
  let report ← comparePrograms "(lam n (error))" "(lam n n)"
  verdict report "inequivalent"
  expect report ["queries", "shared_integer_outputs"] "valid"
  expect report ["queries", "left_sometimes_output"] "falsified"
  let w ← witness report
  expect w ["left"] (Json.mkObj [("kind", toJson "error")])
  expect w ["right"] (Json.mkObj [("kind", toJson "integer"), ("value", ← field w ["input"])])

#eval do
  let report ← comparePrograms "(lam n n)" "(lam n n)" { config with rightSteps := some 0 }
  verdict report "inconclusive"
  expect report ["queries", "left_sometimes_output"] "valid"
  expect report ["queries", "right_sometimes_output"] "falsified"

namespace Validator

def config : _root_.Equivalence.Cli.Config :=
  { Support.config with inputs := "data3", language := "PlutusV2", steps := 1000 }

#eval do
  let report ← comparePrograms "(lam c (con unit ()))" "(lam c (con integer 42))"
    { config with inputs := "data" }
  verdict report "equivalent"
  expect report ["queries", "total_equivalence"] "valid"
  let domain ← IO.ofExcept ((← field report ["input_domain"]).getStr?)
  check report ((domain.splitOn "single script-context argument").length != 1) "Missing single-argument domain"

#eval do
  let report ← comparePrograms
    ("(lam c (force [[[(force (builtin ifThenElse)) " ++
      "[[(builtin equalsData) c] (con data (I 42))]] " ++
      "(delay (error))] (delay (con unit ()))]))")
    "(lam c (con unit ()))" { config with inputs := "data" }
  verdict report "inequivalent"
  let w ← witness report
  expect w ["input"] (Json.mkObj [("int", toJson (42 : Int))])
  expect w ["left"] (Json.mkObj [("kind", toJson "error")])
  expect w ["right"] (Json.mkObj [("kind", toJson "unit")])

#eval do
  let report ← comparePrograms "(lam d (lam r (lam c (con unit ()))))"
    "(lam d (lam r (lam c (con unit ()))))" { config with steps := 0 }
  verdict report "inconclusive"
  expect report ["queries", "total_equivalence"] "falsified"
  noCounterexample report

#eval do
  let report ← comparePrograms
    ("(lam d (lam r (lam c (force [[[(force (builtin ifThenElse)) " ++
      "[[(builtin equalsData) r] (con data (I 42))]] " ++
      "(delay (error))] (delay (con unit ()))]))))")
    "(lam d (lam r (lam c (con unit ()))))" config
  verdict report "inequivalent"
  let w ← witness report
  let input ← IO.ofExcept ((← field w ["input"]).getObj?)
  check report (input.size == 3) "Expected three Data arguments in the witness"
  for name in ["datum", "redeemer", "context"] do
    discard <| field w ["input", name]
  expect w ["input", "redeemer"] (Json.mkObj [("int", toJson (42 : Int))])
  expect w ["left"] (Json.mkObj [("kind", toJson "error")])
  expect w ["right"] (Json.mkObj [("kind", toJson "unit")])

#eval do
  let report ← comparePrograms "(lam d (lam r (lam c (con unit ()))))"
    "(lam d (lam r (lam c (con integer 42))))" config
  verdict report "equivalent"
  expect report ["output_relation"] "acceptance/rejection"

end Validator

end Tests.Equivalence.Cli
