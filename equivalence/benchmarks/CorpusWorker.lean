import Equivalence.Checker

open Lean PlutusCore.UPLC.Term

namespace Corpus

structure Request where
  left : String
  right : String
  validator : Bool
  ecd : Bool := false
  steps : Nat := 5000
  timeout : Nat := 1
  deriving FromJson

def load (path : String) : IO Program := do
  IO.ofExcept <| PlutusCore.UPLC.ScriptEncoding.Internal.singleCborEncodedScriptFromHex?
    (← IO.FS.readFile path).trim

/-- The CLI's unary integer domain measures the explicit slice gcd(x, 462).
Both programs are closed, so embedding the body needs no free-index shift. -/
def adaptEcd : Program → Program
  | .Program version body => .Program version
      (.Lam (.Apply (.Apply body (.Var 0)) (.Const (.Integer 462))))

def verifyEcd (program : Program) : IO Unit := do
  for n in [-12, 0, 6, 48, 1071] do
    let run p args := Equivalence.Function.execute p args 0 0 true false 20000
    unless Equivalence.Function.same
        (run program [.Const (.Integer n), .Const (.Integer 462)])
        (run (adaptEcd program) [.Const (.Integer n)]) == some true do
      throw <| IO.userError s!"ECD adapter replay failed at {n}"

def phase (p : Equivalence.Solver.Phase) : IO Unit := do
  let stderr ← IO.getStderr
  stderr.putStrLn ("[corpus:phase] " ++ (toJson p).compress)
  stderr.flush

end Corpus

def main : IO Unit := do
  let result ← try
    let stdin ← IO.getStdin
    let request : Corpus.Request ← IO.ofExcept <| fromJson? (← IO.ofExcept <| Json.parse (← stdin.readToEnd))
    Corpus.phase { phase := "loading" }
    let mut left ← Corpus.load request.left
    let mut right ← Corpus.load request.right
    if request.ecd then
      Corpus.verifyEcd left
      Corpus.verifyEcd right
      left := Corpus.adaptEcd left
      right := Corpus.adaptEcd right
    let config : Equivalence.Checker.Config := {
      mode := if request.validator then "validator" else "function"
      inputs := if request.validator then "valid-context" else "integer"
      bounded := true, steps := request.steps, timeout := request.timeout
      maxInputs := 1, maxOutputs := 1, maxSigners := 1
      solverSeed := some 0, skipOldRejected := request.validator }
    Equivalence.Checker.check config left right { phase := Corpus.phase }
  catch e => pure <| Equivalence.Checker.report "error" e.toString
  IO.println result.compress
