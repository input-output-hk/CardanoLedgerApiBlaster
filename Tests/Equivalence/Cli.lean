import Equivalence.Cli
import Tests.Equivalence.Support

namespace Tests.Equivalence.Cli
open Support Lean
open _root_.Equivalence
open _root_.Equivalence.Cli (parse)

-- Removed application-specific domains and their selectors are usage errors.
#eval show IO Unit from do
  let c : _root_.Equivalence.Cli.Config := { scripts := #["old", "new"], bounded := true }
  for mode in ["htlc-refund", "htlc-claim", "vesting-full", "vesting-partial",
      "escrow-deposit", "escrow-accept", "escrow-refund"] do
    unless (_root_.Equivalence.Cli.parse c ["--inputs", mode]).toOption.isNone do
      throw <| IO.userError s!"Removed input mode accepted: {mode}"
  for flags in [["--case", "0"], ["--variation", "baseline"], ["--raw-context"]] do
    unless (_root_.Equivalence.Cli.parse c flags).toOption.isNone do
      throw <| IO.userError s!"Removed selector accepted: {flags}"

-- Defaults and explicit overrides are independent of option order.
#eval show IO Unit from do
  let paths := ["old.uplc", "new.uplc"]
  let c ← IO.ofExcept (parse {} (paths ++ ["--mode", "function"]))
  unless c.mode == "function" && c.inputs == "integer" && c.budget.isNone &&
      c.language == "PlutusV3" && c.oldFormat == some "textual" && c.newFormat == some "textual" do
    throw <| IO.userError "Unexpected function defaults"
  unless _root_.Equivalence.Checker.queryNames c == #["function_equivalent"] do
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
  unless explicit.oldFormat.isNone && explicit.format == "flat_hex" do
    throw <| IO.userError "Explicit format lost"
  for (oldSide, newSide) in [("old", "new"), ("left", "right")] do
    let c ← IO.ofExcept (parse {} (paths ++ ["--mode", "function",
      s!"--format-{oldSide}", "blueprint", s!"--validator-{oldSide}", "original",
      s!"--format-{newSide}", "blueprint", s!"--validator-{newSide}", "updated"]))
    unless c.oldFormat == some "blueprint" && c.newFormat == some "blueprint" &&
        c.oldValidator == some "original" && c.newValidator == some "updated" do
      throw <| IO.userError s!"Per-script input options lost for {oldSide}/{newSide}"

#eval show IO Unit from do
  let args := ["old", "new", "--bounded", "--budget", "1", "1"]
  let validator ← IO.ofExcept (parse {} args)
  unless validator.mode == "validator" && validator.bounded do
    throw <| IO.userError "Bounded validator mode was not selected"
  for flags in [["--language-old", "PlutusV2"],
      ["--language-new", "PlutusV3", "--language", "PlutusV2"]] do
    let c ← IO.ofExcept (parse {} (args ++ flags))
    unless c.toConfig.languageFor 0 == "PlutusV2" && c.toConfig.languageFor 1 == "PlutusV3" do
      throw <| IO.userError s!"Per-script language override lost: {flags}"
  for flags in [["--language-old", "PlutusV1"], ["--language-new", "bad"],
      ["--language-old", "PlutusV2", "--split-dispatch"],
      ["--language-old", "PlutusV2", "--mode", "function"]] do
    unless (parse {} (args ++ flags)).toOption.isNone do
      throw <| IO.userError s!"Unsupported language combination accepted: {flags}"

#eval show IO Unit from do
  for options in [["--bounded", "--equivalence"], ["--equivalence", "--bounded"]] do
    let c ← IO.ofExcept (parse {} (["old", "new", "--mode", "function"] ++ options))
    unless c.bounded && c.equivalence do throw <| IO.userError "Bounded equivalence flags lost"

#eval show IO Unit from do
  let paths := ["old.uplc", "new.uplc", "--bounded"]
  let spending ← IO.ofExcept (parse {} paths)
  unless spending.purpose == "spend" do throw <| IO.userError "Expected spending by default"
  let minting := paths ++ ["--purpose", "mint"]
  let c ← IO.ofExcept (parse {} (minting ++ ["--language", "PlutusV2", "--redeemer", "1"]))
  unless c.purpose == "mint" && c.redeemer == some (.I 1) do
    throw <| IO.userError "Minting options were not parsed"
  for flags in [["--datum", "0"], ["--max-earlier-spending-redeemers", "1"], ["--split-dispatch"],
      ["--mode", "function"], ["--language", "PlutusV1"]] do
    unless (parse {} (minting ++ flags)).toOption.isNone do
      throw <| IO.userError s!"Unsupported minting flags accepted: {flags}"

-- Validators have a single structured domain. Function domains remain separate.
#eval show IO Unit from do
  let settings : Cli.Config := { scripts := #["old", "new"], bounded := true }
  let parsed ← IO.ofExcept (Cli.parse settings [])
  unless parsed.inputs == "valid-context" && parsed.maxInputs == 2 &&
      parsed.maxOutputs == 2 && parsed.maxSigners == 2 && parsed.maxEarlierSpendingRedeemers == 0 do
    throw <| IO.userError "Unexpected validator defaults"
  for flag in ["--inputs", "--input"] do
    let c ← IO.ofExcept (Cli.parse settings [flag, "valid-context", "--max-inputs", "3",
      "--max-outputs", "0", "--max-signers", "4", "--max-earlier-spending-redeemers", "1"])
    unless c.maxInputs == 3 && c.maxOutputs == 0 && c.maxSigners == 4 && c.maxEarlierSpendingRedeemers == 1 do
      throw <| IO.userError "Explicit maxima lost"
  for mode in ["integer", "data", "data3", "spending", "small-context", "medium-context"] do
    unless (Cli.parse settings ["--inputs", mode]).toOption.isNone do
      throw <| IO.userError s!"Removed validator mode accepted: {mode}"
  for args in [["--max-inputs", "-1"], ["--max-outputs"], ["--max-signers", "oops"],
      ["--max-earlier-spending-redeemers", "-1"],
      ["--language", "PlutusV2"], ["--raw-context"],
      ["--mode", "function", "--max-inputs", "2"],
      ["--mode", "function", "--max-earlier-spending-redeemers", "0"],
      ["--max-inputs", "2", "--mode", "function"]] do
    unless (Cli.parse settings args).toOption.isNone do
      throw <| IO.userError s!"Invalid profile options accepted: {args}"

#eval show IO Unit from do
  let c ← IO.ofExcept (Cli.parse {} ["old.uplc", "new.uplc", "--bounded", "--steps", "100"])
  unless c.mode == "validator" && c.bounded && c.budget.isNone && c.steps == 100 do
    throw <| IO.userError "Unexpected step-bounded validator defaults"

-- Integer shorthand and alternate spellings share the explicit Data representation.
#eval show IO Unit from do
  let cases : List (String × String) := [
    ("1", "I 1"), ("-42", "I -42"),
    ("123456789012345678901234567890", "I 123456789012345678901234567890"),
    (" 7 ", "I 7"), ("(I 42)", "I 42"), ("B#AB", "B #ab"),
    ("List[I 0]", "List [I 0]"), ("Map[]", "Map []")]
  for flag in ["--datum", "--redeemer"] do
    for (alternate, explicit) in cases do
      let simple ← IO.ofExcept (Cli.parse {} ["old", "new", "--bounded", flag, alternate])
      let typed ← IO.ofExcept (Cli.parse {} ["old", "new", "--bounded", flag, explicit])
      unless simple.datum == typed.datum && simple.redeemer == typed.redeemer do
        throw <| IO.userError s!"Data mismatch: {flag} {alternate}"
    for invalid in ["--json", "", "hello", "\"hello\"", "\"42\"", "1.5", "1e3",
        "I", "B", "Constr", "List", "Map", "(I nope)", "I nope", "I 0 trailing"] do
      unless (Cli.parse {} ["old", "new", "--bounded", flag, invalid]).toOption.isNone do
        throw <| IO.userError s!"Invalid Data accepted: {flag} {invalid}"

-- Exit status is presentation policy; checker verdicts are tested separately.
#eval show IO Unit from do
  for (name, code) in [("bounded_preserved", 0), ("bounded_regression", 1),
      ("inconclusive", 2), ("error", 3), ("vacuously_bounded_preserved", 4)] do
    unless Cli.exitCode (Checker.report name "") == code do
      throw <| IO.userError s!"Unexpected exit code for {name}"

-- A counterexample discovered by native dispatch replay carries that evidence method.
#eval IO.FS.withTempDir fun dir => do
  let input : AssuranceExport.Input := {
    path := dir / "plutus.json", format := "blueprint", bytes := "{}".toUTF8
    blueprint := some { reference := "spend", hash := String.mk (List.replicate 56 '0'), code := "" } }
  let result := Checker.report "bounded_regression" "" [
    ("dispatch", Json.mkObj [("winning_case", Json.mkObj [("native_probe", toJson true)])])]
  let output := dir / "evidence"
  AssuranceExport.write output input input "Preservation" .null result
  let doc ← IO.ofExcept (Json.parse (← IO.FS.readFile (output / "assurance.json")))
  let #[property] ← IO.ofExcept ((← field doc ["properties"]).getArr?)
    | throw <| IO.userError "Expected one assurance property"
  let #[evidence] ← IO.ofExcept ((← field property ["evidence"]).getArr?)
    | throw <| IO.userError "Expected one comparison evidence record"
  expect evidence ["method"] "native-replay"
  expect evidence ["outcome"] "falsified"

end Tests.Equivalence.Cli
