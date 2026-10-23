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
    let selected := selectFamily { config with steps := 300 } mode 0 "baseline"
    let baseline ← comparePrograms negative "(lam c (con unit ()))" selected
    verdict baseline "equivalent"
    noCounterexample baseline
    let varied ← comparePrograms fortyTwo "(lam c (con unit ()))" selected
    verdict varied "inequivalent"
    let w ← witness varied
    let fields ← IO.ofExcept ((← field w ["input", "fields"]).getArr?)
    let txInfo ← IO.ofExcept ((← field fields[0]! ["fields"]).getArr?)
    expect txInfo[3]! ["int"] (42 : Int)
    let readFee := s!"(lam c {fee})"
    let correctType ← comparePrograms readFee "(lam c (con unit ()))" selected
    verdict correctType "equivalent"
    -- Select a family with both optional amounts present, and ensure a
    -- nondefault amount survives symbolic construction and native replay.
    let lastCase := _root_.Equivalence.Cli.caseCount mode - 1
    let treasury := rejectDataAt [0, 14] "Constr 0 [I 42]"
    let present ← comparePrograms treasury "(lam c (con unit ()))"
      (selectFamily selected mode lastCase "baseline")
    verdict present "inequivalent"
    let input ← witness present
    let fields ← IO.ofExcept ((← field input ["input", "fields"]).getArr?)
    let txInfo ← IO.ofExcept ((← field fields[0]! ["fields"]).getArr?)
    expect txInfo[14]! [] (Json.mkObj [("constructor", toJson (0 : Int)),
      ("fields", toJson #[Json.mkObj [("int", toJson (42 : Int))]])])
    expect txInfo[15]! ["constructor"] (0 : Int)

-- These predicates test selection and replay, independently of any submission.
#eval show IO Unit from do
  let modes := #["htlc-refund", "htlc-claim", "vesting-full", "vesting-partial",
    "escrow-refund", "escrow-accept", "escrow-deposit"]
  let selected := { config with steps := 400 }
  checkReferenceWitness selected modes
  withProgram (rejectDataAt [0, 8] "List []") fun script =>
    checkCaseSelection "Shared context" { selected with leftFormat := some "textual" } script.toString #[
      ("htlc-refund", 8, 10), ("htlc-claim", 0, 2),
      ("vesting-full", 16, 20), ("vesting-partial", 64, 81),
      ("escrow-refund", 0, 12), ("escrow-accept", 0, 12), ("escrow-deposit", 0, 12)]

end Tests.Equivalence.Context
