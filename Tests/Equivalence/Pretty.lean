import Equivalence.Cli

namespace Tests.Equivalence.Pretty
open Lean _root_.Equivalence
open PlutusCore.Data (Data)

private def expectText (text fragment : String) : IO Unit := do
  unless (text.splitOn fragment).length > 1 do
    throw <| IO.userError s!"Missing {fragment}:\n{text}"

#eval show IO Unit from do
  let datum := Data.Constr 0 [.Constr 0 [], .I 1000000]
  let raw := ValidContext.context
    { datum, redeemer := .I 1, unused := { fee := .I 8298 }, validRange := Context.range 1000 2000 }
    [{ datum, ada := 75008298 }]
    [{ ada := 75000000 }]
  unless Ledger.validContext raw do throw <| IO.userError "Invalid formatting fixture"
  let witness := Json.mkObj [
    ("input", PlutusCore.Data.toDetailedJson raw),
    ("old", Json.mkObj [("accepts", toJson true),
      ("result", Json.mkObj [("kind", toJson "unit")]), ("spent_cpu", toJson (1000000 : Nat))]),
    ("new", Json.mkObj [("accepts", toJson false), ("kind", toJson "error")]),
    ("replayed", toJson true), ("direction", toJson "old_to_new"),
    ("ledger_validity", Json.mkObj [("valid", toJson true)])]
  let rendered := Equivalence.Pretty.counterexample true witness
  for fragment in ["OLD → NEW", "OLD: accepts (unit); CPU: 1,000,000", "NEW: rejects (error)",
      "Replay: confirmed", "Ledger validation: valid (ledger model)",
      "75,008,298 lovelace (75.008298 ADA)", "75,000,000 lovelace (75.000000 ADA)",
      "Fee: 8,298 lovelace (0.008298 ADA)", "Validity range (POSIX ms): [1,000, 2,000)",
      "(spending input)", "Datum: Constr 0 [Constr 0 [], I 1000000]", "Redeemer: I 1",
      "Inputs:", "Outputs:", "Reference inputs: none", "stake: none", "Mint: empty",
      "Certificates:", "Withdrawals:", "Redeemers:", "Datums:", "Votes:",
      "Proposals:", "Treasury:", "Donation:", "Transaction id:", "Reference script: none"] do
    expectText rendered fragment
  if (rendered.splitOn "\"fields\":").length > 1 then
    throw <| IO.userError "Context text still contains the JSON Data tree"
  -- Arbitrary payload text is exact and can be fed back to the Data parser.
  let payload := Data.Map [(.B "", .List [.I (-42), .Constr 3 [.B "abc"]])]
  let some source := Equivalence.Pretty.dataText (PlutusCore.Data.toDetailedJson payload)
    | throw <| IO.userError "Could not render payload"
  let decoded ← IO.ofExcept (Cli.parseData "--datum" source)
  unless decoded == payload do throw <| IO.userError "Payload text did not round-trip"
  let functionWitness := Json.mkObj [("input", toJson (-42 : Int)),
    ("old", Json.mkObj [("kind", toJson "success"),
      ("result", Json.mkObj [("kind", toJson "integer"), ("value", toJson (42 : Int))])]),
    ("new", Json.mkObj [("kind", toJson "error")]), ("replayed", toJson true)]
  let functionText := Equivalence.Pretty.counterexample false functionWitness
  expectText functionText "Input: -42"
  expectText functionText "OLD: outcome (integer 42)"
  let rawFunctionText := Equivalence.Pretty.counterexample false witness
  expectText rawFunctionText "Input: Constr 0"
  if (rawFunctionText.splitOn "  Context:").length > 1 then
    throw <| IO.userError "Function Data was interpreted as a ledger context"
  let triple := Json.mkObj [("input", Json.mkObj [
    ("datum", PlutusCore.Data.toDetailedJson (.Constr 0 [])),
    ("redeemer", PlutusCore.Data.toDetailedJson (.I 1)),
    ("context", PlutusCore.Data.toDetailedJson (.B "abc"))])]
  let tripleText := Equivalence.Pretty.counterexample false triple
  for fragment in ["Datum: Constr 0 []", "Redeemer: I 1", "Context (Data): B #616263"] do
    expectText tripleText fragment
  -- Negative, large and fractional ADA amounts must not round or overflow.
  let extreme := ValidContext.context { unused := { fee := .I (-1) } }
    [{ ada := 10^30 }] [{ ada := 1 }]
  let some contextText := Equivalence.Pretty.context (PlutusCore.Data.toDetailedJson extreme)
    | throw <| IO.userError "Could not render numeric fixture"
  let numericText := String.intercalate "\n" contextText
  for fragment in ["-1 lovelace (-0.000001 ADA)", "1 lovelace (0.000001 ADA)",
      "1,000,000,000,000,000,000,000,000,000,000 lovelace"] do
    expectText numericText fragment
  let malformed := Json.mkObj [("input", Json.mkObj [("unknown", toJson "payload")])]
  expectText (Equivalence.Pretty.counterexample true malformed) "unknown"

end Tests.Equivalence.Pretty
