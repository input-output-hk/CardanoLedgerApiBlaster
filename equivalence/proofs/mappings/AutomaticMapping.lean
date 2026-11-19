import equivalence.proofs.mappings.MappingSupport
import Blaster

/-!
Start here. Run: lake build MappingExamples

Two small UPLC payout functions, not full ledger validators. Edit the simulated
schemas below: the generator matches quantities by name, reorders arguments,
calculates the unit conversion, supplies extras, and fixes the legacy bonus.
There is no handwritten inputsMatch or percent-to-rate adapter in this file.

Units are the user's semantic hints: 100 percentage units or 10000 fractional
units per whole. Therefore 25% is encoded as 2500/10000 in the new contract.
Metadata is arbitrary; the new bonus feature is disabled for this comparison.
-/
namespace Equivalence.MappingExamples.AutomaticMapping
open Equivalence.MappingExamples.MappingSupport
open PlutusCore.Data (Data)
open PlutusCore.UPLC.PlutusScript (PlutusScript)

-- 1. THE TWO CONTRACTS. Variables refer to arguments, starting at zero from the last.
-- Old(amount, percent) = floor(amount * percent / 100), returning Integer.
def oldContract : PlutusScript := script
  (.Lam (.Lam (payout (.Var 1) (.Var 0) 100)))

-- New(rate, amount, metadata, bonus) = floor(amount * rate / 10000) + bonus,
-- returning Data.I. The body ignores metadata.
def newContract : PlutusScript := script
  (.Lam (.Lam (.Lam (.Lam (.Apply (.Builtin .IData)
    (binary .AddInteger (payout (.Var 2) (.Var 3) 10000) (.Var 0)))))))

-- 2. THE INTERFACE DESCRIPTION / HINTS. This is the part a user supplies today.
def oldSchema : List Quantity := [⟨"amount", 1⟩, ⟨"rate", 100⟩]
def newSchema : List TargetField :=
  [.quantity ⟨"rate", 10000⟩, .quantity ⟨"amount", 1⟩, .extraData, .fixed 0]

-- 3. AUTOMATIC MAPPING. Inference failure makes this declaration fail to compile.
def mapping : Mapping := checkedMapping (inferMapping oldSchema newSchema) (by exact True.intro)
#eval inferMapping oldSchema newSchema
#eval mapping.encode [1000, 25] [.B "arbitrary metadata"]

-- Both scripts are now exposed over the SAME logical input. The new arguments
-- are generated from the schema; the user does not write the conversion function.
def oldArgs (amount percent : Int) (_metadata : Data) := [int amount, int percent]
#mapping_args newArgs mapping

#prep_uplc autoMappingOld oldContract oldArgs 200
#prep_uplc autoMappingNew newContract newArgs 200

-- 4. THIS IS THE CONTRACT-EQUIVALENCE QUERY TO BLASTER.
theorem contracts_equivalent (amount percent : Int) (metadata : Data) :
    observe .integer (autoMappingOld.prop amount percent metadata) =
    observe .dataInteger (autoMappingNew.prop amount percent metadata) := by
  blaster (timeout: 20)

-- 5. THE MAPPING INCLUDES EVERY OLD INPUT: the generated inverse recovers it.
-- New metadata is arbitrary, so this is an embedding of the old information,
-- not a bijection onto every possible new input.
theorem mapping_roundtrip (amount percent : Int) (metadata : Data) :
    (mapping.encode [amount, percent] [metadata]).bind mapping.recover =
      some [amount, percent] := by
  change some [amount * 1 / 1, percent * 100 / 100] = some [amount, percent]
  simp

-- Independently check that both original executions return the same actual
-- value for EVERY input within 200 steps. Equality is not caused by two errors
-- or two exhausted runs. This proof also bypasses the preprocessing optimizer.
theorem executions_return_same_value (amount percent : Int) (metadata : Data) :
    ∃ value, observe .integer (autoMappingOld.exec amount percent metadata) = some value ∧
      observe .dataInteger (autoMappingNew.exec amount percent metadata) = some value := by
  refine ⟨Int.fdiv (amount * percent) 100, rfl, ?_⟩
  change some (Int.fdiv (amount * (percent * 100)) 10000 + 0) =
    some (Int.fdiv (amount * percent) 100)
  rw [Int.add_zero, ← Int.mul_assoc]
  exact congrArg some
    (Int.mul_fdiv_mul_of_pos_left (amount * percent) 100 (by decide : (0 : Int) < 100))

-- Check the code generator against the inferred mapping, with symbolic inputs.
theorem generated_arguments_match (amount percent : Int) (metadata : Data) :
    newArgs amount percent metadata = mapping.arguments [amount, percent] [metadata] := by
  change [int (percent * 100), int amount, .Const (.Data metadata), int 0] =
    [int (percent * 100), int (amount * 1), .Const (.Data metadata), int 0]
  simp

-- Play with concrete inputs here. Both programs return some 250.
#eval observe .integer (autoMappingOld.exec 1000 25 (.I 0))
#eval observe .dataInteger (autoMappingNew.exec 1000 25 (.B "anything"))

-- Trust distinction: mapping_roundtrip is kernel-checked. The Blaster theorem
-- uses the installed SMT backend's blasterProven axiom (no proof reconstruction).
#print axioms mapping_roundtrip
#print axioms executions_return_same_value
#print axioms generated_arguments_match
#print axioms contracts_equivalent

end Equivalence.MappingExamples.AutomaticMapping
