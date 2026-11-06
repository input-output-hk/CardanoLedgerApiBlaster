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
      c.language == "PlutusV3" && c.leftFormat == some "textual" && c.rightFormat == some "textual" do
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
  unless explicit.leftFormat.isNone && explicit.format == "flat_hex" do
    throw <| IO.userError "Explicit format lost"

#eval show IO Unit from do
  let validator ← IO.ofExcept (parse {} ["old", "new", "--bounded", "--budget", "1", "1"])
  unless validator.mode == "validator" && validator.bounded do
    throw <| IO.userError "Bounded validator mode was not selected"

#eval show IO Unit from do
  for options in [["--bounded", "--equivalence"], ["--equivalence", "--bounded"]] do
    let c ← IO.ofExcept (parse {} (["old", "new", "--mode", "function"] ++ options))
    unless c.bounded && c.equivalence do throw <| IO.userError "Bounded equivalence flags lost"

-- Validators have a single structured domain. Function domains remain separate.
#eval show IO Unit from do
  let settings : Cli.Config := { scripts := #["old", "new"], bounded := true }
  let parsed ← IO.ofExcept (Cli.parse settings [])
  unless parsed.inputs == "valid-context" && parsed.maxInputs == 2 &&
      parsed.maxOutputs == 2 && parsed.maxSigners == 2 do
    throw <| IO.userError "Unexpected validator defaults"
  for flag in ["--inputs", "--input"] do
    let c ← IO.ofExcept (Cli.parse settings [flag, "valid-context", "--max-inputs", "3",
      "--max-outputs", "0", "--max-signers", "4"])
    unless c.maxInputs == 3 && c.maxOutputs == 0 && c.maxSigners == 4 do
      throw <| IO.userError "Explicit maxima lost"
  for mode in ["integer", "data", "data3", "spending", "small-context", "medium-context"] do
    unless (Cli.parse settings ["--inputs", mode]).toOption.isNone do
      throw <| IO.userError s!"Removed validator mode accepted: {mode}"
  for args in [["--max-inputs", "-1"], ["--max-outputs"], ["--max-signers", "oops"],
      ["--language", "PlutusV2"], ["--raw-context"],
      ["--mode", "function", "--max-inputs", "2"],
      ["--max-inputs", "2", "--mode", "function"]] do
    unless (Cli.parse settings args).toOption.isNone do
      throw <| IO.userError s!"Invalid profile options accepted: {args}"

#eval show IO Unit from do
  let c ← IO.ofExcept (Cli.parse {} ["old.uplc", "new.uplc", "--bounded", "--steps", "100"])
  unless c.mode == "validator" && c.bounded && c.budget.isNone && c.steps == 100 do
    throw <| IO.userError "Unexpected step-bounded validator defaults"

-- Exit status is presentation policy; checker verdicts are tested separately.
#eval show IO Unit from do
  for (name, code) in [("bounded_preserved", 0), ("bounded_regression", 1),
      ("inconclusive", 2), ("error", 3), ("vacuously_bounded_preserved", 4)] do
    unless Cli.exitCode (Checker.report name "") == code do
      throw <| IO.userError s!"Unexpected exit code for {name}"

end Tests.Equivalence.Cli
