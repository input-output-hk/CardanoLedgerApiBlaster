import PlutusCore.UPLC.BlueprintEncoding.Assurance
import Std.Time

/-! Export a completed comparison as historical evidence for the NEW blueprint. -/

namespace Equivalence.AssuranceExport

open Lean System
open PlutusCore.UPLC.BlueprintEncoding.Assurance.Internal (sha256Hex parseDocument validateReferences)

structure BlueprintScript where
  reference : String
  hash : String
  code : String

structure Input where
  path : FilePath
  format : String
  bytes : ByteArray
  blueprint : Option BlueprintScript := none

private def digest (bytes : ByteArray) : Json :=
  Json.mkObj [("alg", toJson "sha256"), ("digest", toJson (sha256Hex bytes))]

private def Input.report (input : Input) : Json :=
  Json.mkObj ([("path", toJson input.path.toString), ("format", toJson input.format),
    ("fileHash", digest input.bytes)] ++
    (input.blueprint.map fun script =>
      [("validator", toJson script.reference), ("scriptHash", toJson script.hash)]).getD [])

def write (dir : FilePath) (old new : Input) (claim : String) (settings result : Json) : IO Unit := do
  let some target := new.blueprint | throw (IO.userError "Assurance export requires a NEW blueprint")
  let verdict ← IO.ofExcept (result.getObjValAs? String "verdict")
  let outcome := match verdict with
    | "equivalent" | "bounded_equivalent" | "preserved" | "bounded_preserved" => "verified"
    | "inequivalent" | "bounded_inequivalent" | "regression" | "bounded_regression" => "falsified"
    | verdict => if verdict.startsWith "vacuously_" then "partial" else "inconclusive"
  let date := toJson (toString (← Std.Time.PlainDate.now))
  let reportName := "comparison.json"
  let report := (Json.mkObj [
    ("old", old.report), ("new", new.report),
    ("settings", settings), ("result", result)]).pretty ++ "\n"
  let evidence := Json.mkObj [
    ("method", toJson (if (result.getObjVal? "queries").toOption.any
        (fun queries => (queries.getObjValAs? String "program_identity").toOption == some "valid")
      then "program-identity" else "smt-check")),
    ("verifier", toJson "uplc_equiv"), ("tool", toJson "uplc_equiv"),
    ("outcome", toJson outcome), ("date", date), ("scriptHash", toJson target.hash),
    ("artifact", Json.mkObj [
      ("uri", toJson reportName), ("hash", digest report.toUTF8),
      ("mediaType", toJson "application/json")]),
    ("notes", toJson s!"Checker verdict: {verdict}. The artifact identifies OLD and NEW and records the comparison scope.")]
  let doc := Json.mkObj [
    ("$schema", toJson "https://cips.cardano.org/cips/cipXXXX/schemas/assurance.json"),
    ("preamble", Json.mkObj [
      ("title", toJson "UPLC comparison assurance"),
      ("authors", toJson ["uplc_equiv"]), ("created", date)]),
    ("tools", Json.mkObj [("uplc_equiv", Json.mkObj [
      ("name", toJson "uplc_equiv"), ("version", toJson "unversioned")])]),
    ("blueprint", Json.mkObj [
      ("uri", toJson new.path.toString), ("hash", digest new.bytes)]),
    ("properties", toJson [Json.mkObj [
      ("id", toJson "uplc_comparison"),
      ("scope", Json.mkObj [("validators", toJson [target.reference])]),
      ("statement", Json.mkObj [("text", toJson claim)]),
      ("evidence", toJson [evidence])]])]
  let content := doc.pretty ++ "\n"
  let parsed ← IO.ofExcept (parseDocument content)
  IO.ofExcept (validateReferences parsed)
  -- A fresh directory also prevents overwriting either input or an earlier export.
  IO.FS.createDir dir
  IO.FS.writeFile (dir / reportName) report
  IO.FS.writeFile (dir / "assurance.json") content

end Equivalence.AssuranceExport
