import Equivalence.Checker

open Lean PlutusCore.UPLC.Term

-- A fast failure from supplying the wrong argument representation must not look
-- like a useful arithmetic benchmark. Check the unary integer interface natively.
def main : IO Unit := do
  let mut rows : Array Json := #[]
  for group in ["factorial", "factorial_naive_recursion", "fibonacci", "fibonacci_naive_recursion"] do
    for entry in ← System.FilePath.readDir ("equivalence/examples/" ++ group) do
      if entry.path.extension == some "cbor_hex" then
        let program ← IO.ofExcept <|
          PlutusCore.UPLC.ScriptEncoding.Internal.singleCborEncodedScriptFromHex?
            (← IO.FS.readFile entry.path).trim
        let mut observations : Array Json := #[]
        let mut integers := 0
        for n in [0, 1, 5] do
          let result := Equivalence.Function.execute program [.Const (.Integer n)] 0 0 true false 20000
          let fields := match result with
            | .success (.VCon (.Integer value)) _ =>
                [("kind", toJson "integer"), ("value", toJson value)]
            | .error => [("kind", toJson "error")]
            | .unfinished => [("kind", toJson "unfinished")]
            | _ => [("kind", toJson "other")]
          if (fields.head!.2 == toJson "integer") then integers := integers + 1
          observations := observations.push (Json.mkObj (("input", toJson n) :: fields))
        unless integers > 0 do throw <| IO.userError s!"No integer observation: {entry.path}"
        rows := rows.push (Json.mkObj [("script", toJson entry.path.toString),
          ("observations", toJson observations)])
  IO.println (Json.mkObj [("fixture_count", toJson rows.size), ("fixtures", toJson rows)]).pretty
