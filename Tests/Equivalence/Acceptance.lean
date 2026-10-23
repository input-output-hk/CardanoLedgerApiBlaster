import Equivalence.Acceptance

namespace Tests.Equivalence.Acceptance

open _root_.Equivalence.Acceptance
open PlutusCore.UPLC.Term

def unitProgram : Program := .Program (.Version 1 1 0) (.Const .Unit)

-- Exact startup + constant-node boundaries, including zero available budget.
example : accepts true (execute unitProgram [] 16100 200 true) = some true := by decide
example : accepts true (execute unitProgram [] 16099 200 true) = some false := by decide
example : accepts true (execute unitProgram [] 16100 199 true) = some false := by decide
example : accepts true (execute unitProgram [] 0 0 true) = some false := by decide

-- An analysis limit must neither reject nor hide a possible regression.
example : accepts true (execute unitProgram [] 16100 200 true 0) = none := by decide
example : ¬ Preserved true .unfinished .error := by simp [Preserved, accepts]
example : ¬ Regression true .unfinished .error := by simp [Regression, accepts]
example : ¬ Preserved true (.success (.VCon .Unit) ⟨⟨0⟩, ⟨0⟩⟩) .unfinished := by simp [Preserved, accepts]
example : ¬ Regression true (.success (.VCon .Unit) ⟨⟨0⟩, ⟨0⟩⟩) .unfinished := by simp [Regression, accepts]
example : Preserved true .error .unfinished := by simp [Preserved, accepts]
example : Preserved true .unfinished (.success (.VCon .Unit) ⟨⟨0⟩, ⟨0⟩⟩) := by simp [Preserved, accepts]

-- Zero-cost returns still finish at zero remaining budget.
example : accepts true (run .defaultFunSemanticsVariantE
    (.Return [] (.VCon .Unit)) ⟨⟨0⟩, ⟨0⟩⟩ ⟨⟨0⟩, ⟨0⟩⟩ 1) = some true := by decide

end Tests.Equivalence.Acceptance
