import equivalence.proofs.mappings.Relational

/-!
EDIT THIS FILE to try input/output mappings. Build and check with:
  lake build MappingExamples

`mappingRun oldData newData` runs the old and extended UPLC programs, checks the
input mapping, and compares the decoded outputs. `ok` requires valid inputs,
matching input semantics, and successful outputs satisfying the output mapping.

The declarations below simulate blueprint bindings; no inference engine is involved.
The old rate is a percentage. The new rate is a fraction encoded with denominator
10000: 25% = 0.25 = 2500/10000. `metadata` is ignored; `bonus` is a new feature.
-/
namespace Equivalence.MappingExamples.Playground

open Equivalence.MappingExamples.Relational
open PlutusCore.Integer (Integer)
open PlutusCore.Data (Data)

/-! EDIT THESE INPUTS. -/

def oldData : OriginalInput :=
  { amount := 1000, percent := 25 }

def newData : ExtendedInput :=
  { amount := 1000, rateUnits := 2500, metadata := .B "anything", bonus := 0 }

/-! EDIT THESE MAPPINGS to express the correspondence you want to check.
    Unmentioned metadata is unrestricted. Setting bonus = 0 selects legacy behavior.
    The input builders and output decoders live in Relational.lean. -/

def inputsMatch (oldData : OriginalInput) (newData : ExtendedInput) : Bool :=
  newData.amount == oldData.amount &&
  newData.rateUnits == oldData.percent * 100 &&
  newData.bonus == 0

def outputsMatch (oldValue newValue : Integer) : Bool := oldValue == newValue

/-! THE ENTRY POINT. These definitions can stay unchanged while editing inputs. -/

structure MappingResult where
  oldOutput : Option Integer
  newOutput : Option Integer
  validInputs : Bool
  relatedInputs : Bool
  matchingOutputs : Bool
  ok : Bool
  deriving Repr, DecidableEq

-- Unfold the simulated blueprint predicates to make them executable.
instance (a : OriginalInput) : Decidable (OriginalValid a) := by
  unfold OriginalValid
  infer_instance

instance (b : ExtendedInput) : Decidable (ExtendedValid b) := by
  unfold ExtendedValid
  infer_instance

def mappingRun (oldData : OriginalInput) (newData : ExtendedInput) : MappingResult :=
  let oldOutput := originalResult oldData
  let newOutput := extendedResult newData
  let validInputs := decide (OriginalValid oldData ∧ ExtendedValid newData)
  let relatedInputs := inputsMatch oldData newData
  let matchingOutputs := match oldOutput, newOutput with
    | some oldValue, some newValue => outputsMatch oldValue newValue
    | _, _ => false
  { oldOutput, newOutput, validInputs, relatedInputs, matchingOutputs,
    ok := validInputs && relatedInputs && matchingOutputs }

/-! PLAY HERE: a result you can inspect, and a theorem you can check.
    If you change the inputs to disagree, #eval still displays the result, while
    `my_comparison` fails to compile. Comment it out when exploring failing inputs. -/

#eval mappingRun oldData newData

theorem my_comparison : (mappingRun oldData newData).ok = true := by decide

-- Try each change independently. The report explains whether the mapping or output differs.
#eval mappingRun oldData { newData with metadata := .Constr 99 [] } -- still ok
#eval mappingRun oldData { newData with rateUnits := 25 } -- wrong units: payout 2
#eval mappingRun oldData { newData with bonus := 5 } -- new feature: payout 255

/-! UNIVERSAL PROOF: the entry point also works for symbolic inputs.
    This proves every related valid pair passes, not just the numbers above.
    Changing the mappings may require changing this theorem and its proof. -/

theorem mappingRun_correct (a : OriginalInput) (b : ExtendedInput)
    (ha : OriginalValid a) (hmap : Related a b) : (mappingRun a b).ok = true := by
  have hb := related_preserves_validity a b ha hmap
  rcases hmap with ⟨sameAmount, sameRate, legacy⟩
  simp [mappingRun, ha, hb, inputsMatch, outputsMatch, original_evaluates,
    extended_evaluates, sameAmount, sameRate, legacy, scale_preserves_payout]

/-- An arbitrary metadata field does not require a user-supplied default. -/
theorem arbitrary_metadata (a : OriginalInput) (ha : OriginalValid a) (metadata : Data) :
    (mappingRun a (adapt a metadata)).ok = true :=
  mappingRun_correct a _ ha (adapt_related a metadata)

/-! Regression checks independent of the editable oldData/newData above. -/

example : (mappingRun ⟨1000, 25⟩ ⟨25, 1000, .I 0, 0⟩).ok = false := by decide
example : (mappingRun ⟨1000, 25⟩ ⟨2500, 1000, .I 0, 5⟩).ok = false := by decide

-- Accidental output equality is insufficient: both return 0, but units do not match.
example : (mappingRun ⟨0, 25⟩ ⟨25, 0, .I 0, 0⟩).matchingOutputs = true := by decide
example : (mappingRun ⟨0, 25⟩ ⟨25, 0, .I 0, 0⟩).ok = false := by decide

-- Even related inputs with matching results must satisfy the declared domains.
example : (mappingRun ⟨1000, 101⟩ ⟨10100, 1000, .I 0, 0⟩).ok = false := by decide

#print axioms my_comparison
#print axioms mappingRun_correct

end Equivalence.MappingExamples.Playground
