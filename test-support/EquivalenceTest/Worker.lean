import EquivalenceTest.Protocol

open Lean EquivalenceTest

@[extern "lean_internal_set_max_memory"]
opaque setTestMaxMemory (bytes : USize) : BaseIO Unit

/-- Native isolation for library tests; no command-line checker code is imported. -/
def main : IO Unit := do
  setTestMaxMemory (8192 * 1024 * 1024)
  let result ← try
    let stdin ← IO.getStdin
    let json ← IO.ofExcept (Json.parse (← stdin.readToEnd))
    let request : Protocol.Request ← IO.ofExcept (fromJson? json)
    let old ← IO.ofExcept (Protocol.decode request.old)
    let new ← IO.ofExcept (Protocol.decode request.new)
    Equivalence.Checker.check request.options old new
  catch error => pure (Equivalence.Checker.report "error" error.toString)
  IO.println result.compress
