import Tests.Equivalence.Support

namespace Tests.Equivalence.Acceptance

open _root_.Equivalence.Acceptance
open PlutusCore.UPLC.Term
open Support

def unitProgram : Program := .Program (.Version 1 1 0) (.Const .Unit)

-- These real scripts must reject before symbolic recursion expands. The V2
-- case also checks this independently of the V3 unit-return requirement.
#eval show IO Unit from do
  for language in ["PlutusV3", "PlutusV2"] do
    let report ← runBounded {
      scripts := #["equivalence/examples/factorial/Plutarch_1.11.0_SeungheonOh_size.cbor_hex",
        "equivalence/examples/factorial/Scalus_0.17.0_Unisay.cbor_hex"]
      inputs := "integer"
      language
      budget := some (100000, 10000)
      wallTimeout := 5 }
    verdict report "vacuously_preserved"
    expect report ["queries", "old_rejected"] "valid"

#eval show IO Unit from do
  for (cpu, memory, symmetric, mode, language) in [
      (100, 100, false, "valid-context", "PlutusV3"),
      (100, 100, true, "valid-context", "PlutusV3"),
      (100, 100, false, "data", "PlutusV3"),
      (16099, 200, false, "valid-context", "PlutusV3"),
      (16100, 199, false, "data", "PlutusV2")] do
    let report ← runBounded {
      scripts := #["equivalence/examples/linear_vesting/Plinth_1.45.0.0_Unisay.cbor_hex",
        "equivalence/examples/linear_vesting/Plinth_1.67.0.0_Unisay.cbor_hex"]
      inputs := mode
      language
      equivalence := symmetric
      budget := some (cpu, memory)
      timeout := 1
      wallTimeout := 5 }
    verdict report (if symmetric then "vacuously_equivalent" else "vacuously_preserved")
    expect report ["vacuity_reason"] "initial_step_budget_exhausted"

#eval show IO Unit from do
  let report ← runBounded {
    scripts := #["equivalence/examples/ecd/Plinth_1.45.0.0_Unisay.cbor_hex",
      "equivalence/examples/ecd/Plinth_1.67.0.0_Unisay.cbor_hex"]
    budget := some (1, 1) }
  verdict report "vacuously_preserved"
  expect report ["vacuity_reason"] "startup_budget_exhausted"

-- An analysis limit must neither reject nor hide a possible regression.
example : accepts true (execute unitProgram [] 16100 200 true 0) = none := by decide

-- Any applied script needs startup plus its first application charge. This
-- must be decided independently of its body and symbolic argument.
example (program : Program) (arg : Term) :
    execute program [arg] 100 100 true = .budgetExhausted := by cases program; rfl
example (program : Program) (arg : Term) :
    execute program [arg] 100 100 true 0 = .unfinished := by cases program; rfl
example : accepts true (execute unitProgram [] 16100 200 true 2) = some true := by decide
example : accepts true (execute unitProgram [] 16099 200 true 2) = some false := by decide
example : accepts true (execute unitProgram [] 16100 199 true 2) = some false := by decide

def referenceRun (variant : PlutusCore.Default.BuiltinSemanticsVariant)
    (state : PlutusCore.UPLC.CekMachine.State)
    (remaining initial : PlutusCore.UPLC.ExBudget.ExBudget) (guard : Nat) : Result :=
  match PlutusCore.UPLC.CekMachine.EvaluationResult.ofCostedRun remaining
      (PlutusCore.UPLC.CekMachine.runStepsWithCost variant state guard) with
  | .Success value spent => .success value (initial - (remaining - spent))
  | .EvaluationError => .error
  | .BudgetExhausted _ => .budgetExhausted
  | .StepLimitReached _ => .unfinished

def checkDeferred (program : Program) (args : List Term) (cpu memory : Nat)
    (v3 : Bool) (guard : Nat) : IO Unit := do
  let variant : PlutusCore.Default.BuiltinSemanticsVariant :=
    if v3 then .defaultFunSemanticsVariantE else .defaultFunSemanticsVariantD
  let budget : PlutusCore.UPLC.ExBudget.ExBudget := ⟨⟨cpu⟩, ⟨memory⟩⟩
  let startup := (PlutusCore.UPLC.CekMachine.semVarToCosts variant).startupCost
  let expected := if budget.canAfford startup then
    match program with
    | .Program _ body => referenceRun variant
        (PlutusCore.UPLC.CekMachine.initialState (PlutusCore.UPLC.CekMachine.applyParams body args))
        (budget - startup) budget guard
    else .budgetExhausted
  let actual := execute program args cpu memory v3 guard
  unless reprStr actual == reprStr expected do
    throw <| IO.userError s!"Budgeting disagrees for {reprStr args} at {cpu}/{memory}, guard {guard}, v3={v3}: {reprStr actual} != {reprStr expected}"

-- Early machine charging agrees with the independent upstream deferred-cost
-- runner, including builtins, divergence, exact bounds and guard exhaustion.
#eval show IO Unit from do
  let self := Term.Lam (.Apply (.Var 0) (.Var 0))
  let programs := [unitProgram, Program.Program (.Version 1 1 0) .Error,
    Program.Program (.Version 1 1 0) (.Lam (.Const .Unit)),
    Program.Program (.Version 1 1 0) (.Apply (.Apply (.Builtin .AddInteger)
      (.Const (.Integer 1))) (.Const (.Integer 2))),
    Program.Program (.Version 1 1 0) (.Apply self self)]
  for program in programs do
    for args in [[], [.Const (.Integer 0)]] do
      for v3 in [false, true] do
        for (cpu, memory) in [(1, 1), (100, 100), (16099, 200), (16100, 199),
            (16100, 200), (64099, 500), (64100, 500), (1000000, 10000),
            (1024099, 6500), (1024100, 6500), (1600099, 10100), (1600100, 10100)] do
          for guard in [0, 1, 2, 100] do
            checkDeferred program args cpu memory v3 guard

#eval show IO Unit from do
  for file in ["Plutarch_1.11.0_SeungheonOh_size", "Scalus_0.17.0_Unisay"] do
    let program ← _root_.Equivalence.Cli.readProgram
      s!"equivalence/examples/factorial/{file}.cbor_hex" "single_cbor_hex"
    for n in ([-5, 0, 1, 5, 12] : List Int) do
      for v3 in [false, true] do
        for (cpu, memory) in [(100000, 10000), (471985, 2302), (471986, 2302),
            (1000000, 10000), (20000000, 100000)] do
          for guard in [0, 5, 30, 1000] do
            checkDeferred program [.Const (.Integer n)] cpu memory v3 guard
example : ¬ Preserved true .unfinished .error := by simp [Preserved, accepts]
example : ¬ Regression true .unfinished .error := by simp [Regression, accepts]
example : ¬ Preserved true (.success (.VCon .Unit) ⟨⟨0⟩, ⟨0⟩⟩) .unfinished := by simp [Preserved, accepts]
example : ¬ Regression true (.success (.VCon .Unit) ⟨⟨0⟩, ⟨0⟩⟩) .unfinished := by simp [Regression, accepts]
example : Preserved true .error .unfinished := by simp [Preserved, accepts]
example : Preserved true .unfinished (.success (.VCon .Unit) ⟨⟨0⟩, ⟨0⟩⟩) := by simp [Preserved, accepts]

-- Both directions must be established before reporting equivalence.
#eval show IO Unit from do
  let config : _root_.Equivalence.Cli.Config := { equivalence := true, inputs := "data", budget := some (1, 1) }
  let results := (_root_.Equivalence.Cli.queryNames config).map fun name =>
    if name == "acceptance_preserved" || name == "no_acceptance_regression" then
      Blaster.Smt.Result.Valid else .Undetermined
  let result := _root_.Equivalence.Cli.classify config results unitProgram unitProgram
  unless (result.getObjValAs? String "verdict").toOption == some "inconclusive" do
    throw <| IO.userError result.pretty

-- A completed implication without either rejection proof or acceptance witness
-- remains inconclusive, even if the solver supplied a non-replayable model.
#eval show IO Unit from do
  let config : _root_.Equivalence.Cli.Config := { inputs := "integer", budget := some (1000000, 10000) }
  let results := (_root_.Equivalence.Cli.queryNames config).map fun name =>
    if name == "old_rejected" then Blaster.Smt.Result.Falsified [] else .Valid
  let result := _root_.Equivalence.Cli.classify config results unitProgram unitProgram
  unless (result.getObjValAs? String "verdict").toOption == some "inconclusive" &&
      (result.getObjValAs? String "old_acceptance_status").toOption == some "unestablished" do
    throw <| IO.userError result.pretty

end Tests.Equivalence.Acceptance
