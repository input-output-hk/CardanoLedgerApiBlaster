import Tests.Equivalence.Support

namespace Tests.Equivalence.Variations

open Support Lean

set_option stderrAsMessages false

/-- A synthetic predicate distinguishes a variation from its baseline. Replaying
    its witness checks that solving and reconstruction use the same context. -/
def checkVariation (selected : _root_.Equivalence.Cli.Config)
    (variation term expected : String) (checkBaseline := true) : IO Unit := do
  progress s!"Context variation regression: {selected.inputs}, {variation}"
  let inspect := rejectIf s!"[[(builtin equalsData) {term}] (con data ({expected}))]"
  if checkBaseline then
    let baseline ← comparePrograms inspect "(lam c (con unit ()))" selected
    verdict baseline "equivalent"
    noCounterexample baseline
  let varied ← comparePrograms inspect "(lam c (con unit ()))" { selected with variation }
  verdict varied "inequivalent"
  let w ← witness varied
  expect w ["old", "accepts"] false
  expect w ["new", "accepts"] true
  let domain ← IO.ofExcept ((← field varied ["input_domain"]).getStr?)
  check varied ((domain.splitOn s!"context variation: {variation}:").length != 1)
    "Variation missing from input domain"

#eval show IO Unit from do
  -- Exercise each transformation once; shared case-selection tests cover both
  -- HTLC branches. Hash opacity prevents proving its baseline is nonempty.
  let groups : Array (String × Nat × Array (String × List Nat × String)) := #[
    ("htlc-refund", 10, #[
      ("datum-timeout-101", [2, 1, 0, 3], "I 101"),
      ("payer", [2, 1, 0, 0, 0, 0], "B #6f746865722d7061796572"),
      ("secret-wrong", [1], "Constr 0 [B #77726f6e67]"),
      ("signer-second", [0, 8], "List [B #6f746865722d7369676e6572, B #7061796572]")]),
    ("htlc-claim", 10, #[
      ("datum-malformed", [2, 1, 0], "I 0"),
      ("hash-empty", [2, 1, 0, 2], "B #"),
      ("redeemer-tag", [1], "Constr 2 []"),
      ("redeemer-fields", [1], "Constr 0 [I 42]"),
      ("upper-inclusive", [0, 7, 1, 1], "Constr 1 []")]),
    ("vesting-partial", 81, #[
      ("datum-schedule", [2, 1, 0, 5], "I 20"),
      ("datum-malformed", [2, 1, 0], "I 0"),
      ("asset-policy", [2, 1, 0, 1, 0], "B #6f746865722d706f6c696379"),
      ("beneficiary", [2, 1, 0, 0, 0, 0], "B #6f746865722d62656e6566696369617279"),
      ("redeemer-tag", [1], "Constr 2 []"),
      ("redeemer-fields", [1], "Constr 0 [I 42]"),
      ("signer-second", [0, 8], "List [B #6f746865722d7369676e6572, B #62656e6566696369617279]"),
      ("outputs-empty", [0, 2], "List []"),
      ("time-49", [0, 7, 0, 0, 0], "I 49")]),
    ("escrow-refund", 12, #[
      ("datum-malformed", [2, 1, 0], "I 0"),
      ("lower-infinite", [0, 7, 0, 0], "Constr 0 []"),
      ("upper-infinite", [0, 7, 1, 0], "Constr 2 []")])]
  for (mode, index, probes) in groups do
    let selected := selectFamily config mode index "baseline"
    for (variation, path, expected) in probes do
      checkVariation selected variation (contextFieldTerm path) expected (variation != "hash-empty")

-- A composed write covers datum-total together with the shared fee variation.
#eval do
  let inspect := rejectDataAt [2, 1, 0, 2] "I 1001"
  let selected := selectFamily config "vesting-partial" 81 "baseline"
  let baseline ← comparePrograms inspect "(lam c (con unit ()))" selected
  verdict baseline "equivalent"
  for variation in ["fee-positive,datum-total", "datum-total, fee-positive"] do
    let report ← comparePrograms inspect "(lam c (con unit ()))" { selected with variation }
    verdict report "inequivalent"
    let w ← witness report
    let input ← field w ["input"]
    expect (← dataField input [0, 3]) ["int"] (1 : Int)
    expect (← dataField input [2, 1, 0, 2]) ["int"] (1001 : Int)
    let domain ← IO.ofExcept ((← field report ["input_domain"]).getStr?)
    check report ((domain.splitOn s!"context variation: {variation}:").length == 2) "Missing composition description"

-- Later writes to the same redeemer field win; a field-only write keeps its tag.
#eval do
  for (variation, text, expected) in [
      ("redeemer-fields,redeemer-tag", "Constr 2 []", _root_.Equivalence.Model.dataJson (.Constr 2 [])),
      ("redeemer-tag,redeemer-fields", "Constr 2 [I 42]", _root_.Equivalence.Model.dataJson (.Constr 2 [.I 42]))] do
    let report ← comparePrograms (rejectDataAt [1] text) "(lam c (con unit ()))"
      (selectFamily config "htlc-claim" 10 variation)
    verdict report "inequivalent"
    let w ← witness report
    expect (← dataField (← field w ["input"]) [1]) [] expected

-- Changed authorization must not leave an arbitrary tail ahead of a missing
-- signer. Otherwise the analysis guard cannot cover the inspected list.
#eval show IO Unit from do
  for (mode, index, variation, signer) in [
      ("htlc-refund", 10, "payer", "7061796572"),
      ("htlc-claim", 10, "recipient", "726563697069656e74"),
      ("vesting-full", 20, "beneficiary", "62656e6566696369617279"),
      ("vesting-partial", 81, "beneficiary", "62656e6566696369617279")] do
    let selected := selectFamily config mode index variation
    let report ← comparePrograms (rejectDataAt [0, 8] s!"List [B #{signer}]")
      "(lam c (error))" selected
    verdict report "equivalent"
  let selected := selectFamily config "htlc-refund" 10 "secret-empty"
  let firstSigner := s!"[(force (builtin headList)) [(builtin unListData) {contextFieldTerm [0, 8]}]]"
  let recipient := rejectIf s!"[[(builtin equalsData) {firstSigner}] (con data (B #726563697069656e74))]"
  for inspect in [recipient, rejectDataAt [0, 7, 1, 0, 0] "I 102"] do
    let report ← comparePrograms inspect "(lam c (error))" selected
    verdict report "equivalent"

end Tests.Equivalence.Variations
