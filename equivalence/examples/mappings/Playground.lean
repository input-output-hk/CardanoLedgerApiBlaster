import Equivalence.Checker

/-!
Run from the repository root, with Z3 5.4.0 on PATH:
  lake build uplc_equiv
  lake env lean equivalence/examples/mappings/Playground.lean

Edit the schemas below. The checker generates the adapter and compares the two
original UPLC functions. Change new rate units to 100 or bonus to 5 to obtain a
replayed counterexample. These are functions, not full ledger validators.
-/
namespace MappingPlayground
open Lean Equivalence
open PlutusCore.UPLC.Term (Program)

def schema : Mapping.Spec := {
  source := [⟨"amount", 1⟩, ⟨"rate", 100⟩]
  target := [.quantity ⟨"rate", 10000⟩, .quantity ⟨"amount", 1⟩, .extraData, .fixed 0]
  oldOutput := .integer
  newOutput := .dataInteger }

-- The generated conversion encodes 25% as 2500/10000. Metadata is arbitrary.
#eval Mapping.infer schema
#eval (Mapping.infer schema).toOption.bind fun plan => plan.encode [1000, 25] [.B "anything"]

def mappingRun (old new : Program) : IO Json :=
  Checker.check {
    mode := "function"
    inputs := "integer"
    mapping := some schema
    steps := 200
    timeout := 20 } old new

#eval show IO Unit from do
  let read := fun path => do
    IO.ofExcept (PlutusCore.UPLC.TextEncoding.programFromString (← IO.FS.readFile path))
  let old ← read "equivalence/examples/mappings/old.uplc"
  let new ← read "equivalence/examples/mappings/new.uplc"
  IO.println (← mappingRun old new).pretty

end MappingPlayground
