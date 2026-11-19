import equivalence.proofs.mappings.AutomaticMapping

namespace Equivalence.MappingExamples.MappingSupportTests
open Equivalence.MappingExamples.MappingSupport
open Equivalence.MappingExamples.AutomaticMapping

-- Inference must reject ambiguous, lossy, or incomplete interface descriptions.
example : inferMapping [⟨"rate", 100⟩, ⟨"rate", 100⟩] [] =
    .error "Ambiguous source quantity names" := rfl
example : inferMapping [⟨"rate", 0⟩] [.quantity ⟨"rate", 100⟩] =
    .error "Source units must be positive" := rfl
example : inferMapping [⟨"rate", 100⟩] [.quantity ⟨"price", 100⟩] =
    .error "No source quantity named price" := rfl
example : inferMapping [⟨"rate", 10000⟩] [.quantity ⟨"rate", 100⟩] =
    .error "No exact integer unit expansion for rate" := rfl
example : inferMapping [⟨"rate", 100⟩] [.quantity ⟨"rate", 0⟩] =
    .error "No exact integer unit expansion for rate" := rfl
example : inferMapping [⟨"rate", 100⟩] [.extraData] =
    .error "A source quantity is missing from the target" := rfl

-- Exercise the same generator on different names, units, and argument positions.
private def secondMapping := checkedMapping
  (inferMapping [⟨"time", 1⟩, ⟨"value", 1⟩]
    [.fixed 7, .quantity ⟨"value", 1⟩, .quantity ⟨"time", 1000⟩])
  (by exact True.intro)

example : secondMapping.encode [2, 9] [] =
    some [.integer 7, .integer 9, .integer 2000] := rfl
example : secondMapping.recover [.integer 7, .integer 9, .integer 2000] = some [2, 9] := rfl
example : secondMapping.encode [2] [] = none := rfl
example : secondMapping.encode [2, 9] [.I 0] = none := rfl
example : secondMapping.recover [.integer 7] = none := rfl

-- Exercise code generation as well as the interpreter, including signed constants.
#mapping_args secondArgs secondMapping
example : secondArgs 2 9 = [int 7, int 9, int 2000] := rfl

private def negativeMapping := checkedMapping
  (inferMapping [] [.fixed (-7)]) (by exact True.intro)
#mapping_args negativeArgs negativeMapping
example : negativeArgs = [int (-7)] := rfl

-- The generated code must match the inferred interpreter for symbolic values.
example (time value : Int) : secondArgs time value = secondMapping.arguments [time, value] [] := by
  change [int 7, int value, int (time * 1000)] = [int 7, int (value * 1), int (time * 1000)]
  simp

-- Structurally valid mappings can still be semantically wrong. Check the
-- generated adapter against the actual two programs, not just the interpreter.
private def wrongScale := checkedMapping
  (inferMapping oldSchema
    [.quantity ⟨"rate", 100⟩, .quantity ⟨"amount", 1⟩, .extraData, .fixed 0])
  (by exact True.intro)
#mapping_args wrongScaleArgs wrongScale
#prep_uplc mappingTestWrongScale newContract wrongScaleArgs 200

example : observe .dataInteger (mappingTestWrongScale.exec 1000 25 (.I 0)) = some 2 := rfl
example : observe .integer (autoMappingOld.exec 1000 25 (.I 0)) ≠
    observe .dataInteger (mappingTestWrongScale.exec 1000 25 (.I 0)) := by decide

private def enabledFeature := checkedMapping
  (inferMapping oldSchema
    [.quantity ⟨"rate", 10000⟩, .quantity ⟨"amount", 1⟩, .extraData, .fixed 5])
  (by exact True.intro)
#mapping_args enabledFeatureArgs enabledFeature
#prep_uplc mappingTestBonus newContract enabledFeatureArgs 200

example : observe .dataInteger (mappingTestBonus.exec 1000 25 (.I 0)) = some 255 := rfl
example : observe .integer (autoMappingOld.exec 1000 25 (.I 0)) ≠
    observe .dataInteger (mappingTestBonus.exec 1000 25 (.I 0)) := by decide

end Equivalence.MappingExamples.MappingSupportTests
