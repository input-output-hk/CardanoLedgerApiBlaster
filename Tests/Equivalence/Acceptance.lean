import Equivalence.Cli

namespace Tests.Equivalence.Acceptance

open _root_.Equivalence.Acceptance
open PlutusCore.UPLC.Term

def unitProgram : Program := .Program (.Version 1 1 0) (.Const .Unit)

-- An analysis limit must neither reject nor hide a possible regression.
example : accepts true (execute unitProgram [] 16100 200 true 0) = none := by decide
example : ¬ Preserved true .unfinished .error := by simp [Preserved, accepts]
example : ¬ Regression true .unfinished .error := by simp [Regression, accepts]
example : ¬ Preserved true (.success (.VCon .Unit) ⟨⟨0⟩, ⟨0⟩⟩) .unfinished := by simp [Preserved, accepts]
example : ¬ Regression true (.success (.VCon .Unit) ⟨⟨0⟩, ⟨0⟩⟩) .unfinished := by simp [Regression, accepts]
example : Preserved true .error .unfinished := by simp [Preserved, accepts]
example : Preserved true .unfinished (.success (.VCon .Unit) ⟨⟨0⟩, ⟨0⟩⟩) := by simp [Preserved, accepts]

-- Both directions must be established before reporting equivalence.
#eval show IO Unit from do
  let config : _root_.Equivalence.Cli.Config := { equivalence := true, budget := some (1, 1) }
  let result := _root_.Equivalence.Cli.classify config #[.Valid, .Valid, .Undetermined, .Undetermined] unitProgram unitProgram
  unless (result.getObjValAs? String "verdict").toOption == some "inconclusive" do
    throw <| IO.userError result.pretty

end Tests.Equivalence.Acceptance
