import Tests.Equivalence.Support

namespace Tests.Equivalence.Context

open Support Lean

set_option stderrAsMessages false

-- All scenarios use exactly the same fee domain: integers of arbitrary
-- nonnegative magnitude. Negative fees and incorrect outer encodings cannot
-- supply a baseline mismatch; a positive fee must still supply a real model.
#eval show IO Unit from do
  let fee := s!"[(builtin unIData) {contextFieldTerm [0, 3]}]"
  let negative := rejectIf s!"[[(builtin lessThanInteger) {fee}] (con integer 0)]"
  let fortyTwo := rejectIf s!"[[(builtin equalsInteger) {fee}] (con integer 42)]"
  for mode in ["htlc-refund", "htlc-claim", "vesting-full", "vesting-partial",
      "escrow-refund", "escrow-accept", "escrow-deposit"] do
    progress s!"Shared context regression: {mode}, fee domain"
    let selected := selectFamily config mode 0 "baseline"
    let baseline ← comparePrograms negative "(lam c (con unit ()))" selected
    verdict baseline "equivalent"
    noCounterexample baseline
    let varied ← comparePrograms fortyTwo "(lam c (con unit ()))" selected
    verdict varied "inequivalent"
    let w ← witness varied
    expect (← dataField (← field w ["input"]) [0, 3]) ["int"] (42 : Int)
    -- Select a family with both optional amounts present, and ensure a
    -- nondefault amount survives symbolic construction and native replay.
    let lastCase := _root_.Equivalence.Cli.caseCount mode - 1
    let treasury := rejectDataAt [0, 14] "Constr 0 [I 42]"
    let present ← comparePrograms treasury "(lam c (con unit ()))"
      (selectFamily selected mode lastCase "baseline")
    verdict present "inequivalent"
    let input ← field (← witness present) ["input"]
    expect (← dataField input [0, 14]) [] (Json.mkObj [("constructor", toJson (0 : Int)),
      ("fields", toJson #[Json.mkObj [("int", toJson (42 : Int))]])])
    expect (← dataField input [0, 15]) ["constructor"] (0 : Int)

-- These predicates test selection and replay, independently of any submission.
#eval show IO Unit from do
  let selected := config
  withProgram (rejectDataAt [0, 8] "List []") fun script =>
    checkCaseSelection "Shared context" { selected with leftFormat := some "textual" } script.toString #[
      ("htlc-refund", 8, 10), ("htlc-claim", 0, 2),
      ("vesting-full", 16, 20), ("vesting-partial", 64, 81),
      ("escrow-refund", 0, 12), ("escrow-accept", 0, 12), ("escrow-deposit", 0, 12)]

-- Independently quantified times must survive construction, solving and replay.
#eval do
  let equalAt := fun (path : List Nat) (n : Int) => s!"[[(builtin equalsInteger) [(builtin unIData) {contextFieldTerm path}]] (con integer {n})]"
  let condition := s!"[[[(force (builtin ifThenElse)) {equalAt [0, 7, 0, 0, 0] (42 : Int)}] {equalAt [0, 7, 1, 0, 0] (-17)}] (con bool False)]"
  let selected := selectFamily { acceptanceConfig with budget := some (100000000, 1000000) } "vesting-partial" 81 "time-any"
  let report ← comparePrograms "(lam c (con unit ()))" (rejectIf condition) selected
  verdict report "regression"
  let w ← witness report
  let input ← field w ["input"]
  expect (← dataField input [0, 7, 0, 0, 0]) ["int"] (42 : Int)
  expect (← dataField input [0, 7, 1, 0, 0]) ["int"] (-17 : Int)

-- Generalized datum/redeemer symbols must not alias each other or raw fields.
#eval do
  let conditions : List (List Nat × Int) := [([2, 1, 0], 11), ([1], 22), ([0, 3], 33)]
  let condition := conditions.foldr (fun (entry : List Nat × Int) (rest : String) =>
    s!"[[[(force (builtin ifThenElse)) [[(builtin equalsInteger) [(builtin unIData) {contextFieldTerm entry.1}]] (con integer {entry.2})]] {rest}] (con bool False)]") "(con bool True)"
  let onlyAccept := "(lam c (force [[[(force (builtin ifThenElse)) " ++ condition ++
    "] (delay (con unit ()))] (delay (error))]))"
  let selected := selectFamily { acceptanceConfig with budget := some (100000000, 1000000) } "htlc-refund" 0 "datum-any,redeemer-any,raw-unused"
  let report ← comparePrograms onlyAccept "(lam c (error))" selected
  verdict report "regression"
  let w ← witness report
  let input ← field w ["input"]
  for (path, expected) in conditions do
    expect (← dataField input path) ["int"] expected

-- The unrestricted spending builder still supplies the common V3 outer shape.
#eval do
  let report ← comparePrograms "(lam c (con unit ()))" "(lam c (error))"
    { acceptanceConfig with inputs := "spending" }
  verdict report "regression"
  let w ← witness report
  expect w ["input", "constructor"] (0 : Nat)
  let fields ← IO.ofExcept ((← field w ["input", "fields"]).getArr?)
  check report (fields.size == 3) "Expected three script-context fields"
  let tx ← IO.ofExcept ((← field fields[0]! ["fields"]).getArr?)
  check report (tx.size == 16) "Expected 16 TxInfo fields"
  expect fields[2]! ["constructor"] (1 : Nat)
  let info ← IO.ofExcept ((← field fields[2]! ["fields"]).getArr?)
  check report (info.size == 2) "Expected spending reference and datum option"

end Tests.Equivalence.Context
