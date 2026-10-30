import PlutusCore.UPLC

namespace Equivalence.Acceptance

open PlutusCore.Default
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue (CekValue)
open PlutusCore.UPLC.ExBudget (ExBudget)
open PlutusCore.UPLC.Term (Program Term BuiltinFun)

inductive Result where
  | success : CekValue → ExBudget → Result
  | error
  | budgetExhausted
  | unfinished
deriving Repr

/-- Machine charges have already been paid. Check the recorded builtin charges
    against the remaining budget and retain the analysis-limit distinction. -/
def finish (variant : BuiltinSemanticsVariant) (state : State)
    (remaining initial : ExBudget) (calls : List (BuiltinFun × List CekValue)) : Result :=
  match EvaluationResult.ofCostedRun remaining (state, builtinCallsCost variant calls) with
  | .Success value spent => .success value (initial - (remaining - spent))
  | .EvaluationError => .error
  | .BudgetExhausted _ => .budgetExhausted
  | .StepLimitReached _ => .unfinished

/-- Check fixed machine charges early, without introducing a symbolic budget
    branch on each input-dependent builtin cost. Builtins are costed at the end. -/
def runWithMachineBudget (variant : BuiltinSemanticsVariant) (state : State)
    (remaining initial : ExBudget) (guard : Nat)
    (calls : List (BuiltinFun × List CekValue)) : Result :=
  match guard, state with
  | _, .Halt _ | _, .Error | 0, _ => finish variant state remaining initial calls
  | fuel + 1, _ =>
    let charge := calculateStepCostr (semVarToCosts variant) state
    if remaining.canAfford charge then
      let calls := match saturatedBuiltin? state with
        | some call => call :: calls
        | none => calls
      runWithMachineBudget variant (step variant state) (remaining - charge) initial fuel calls
    else .budgetExhausted

def runDeferred (variant : BuiltinSemanticsVariant) (state : State)
    (remaining initial : ExBudget) (guard : Nat) : Result :=
  match EvaluationResult.ofCostedRun remaining (runStepsWithCost variant state guard) with
  | .Success value spent => .success value (initial - (remaining - spent))
  | .EvaluationError => .error
  | .BudgetExhausted _ => .budgetExhausted
  | .StepLimitReached _ => .unfinished

/-- A componentwise upper bound on machine charges within the analysis guard.
    Return, halt and error transitions cost zero. -/
def machineBudgetBound (variant : BuiltinSemanticsVariant) (guard : Nat) : ExBudget :=
  let costs := semVarToCosts variant
  let charges := [costs.stepCostVar, costs.stepCostConst, costs.stepCostLam,
    costs.stepCostDelay, costs.stepCostForce, costs.stepCostApply,
    costs.stepCostBuiltin, costs.stepCostConstr, costs.stepCostCase]
  let cpu := charges.foldl (fun largest charge => max largest charge.exBudgetCPU.unExCPU) 0
  let memory := charges.foldl (fun largest charge => max largest charge.exBudgetMemory.unExMemory) 0
  ⟨⟨cpu * guard⟩, ⟨memory * guard⟩⟩

/-- Omit machine-budget checks only when the budget covers every possible
    machine charge within the guard. Otherwise check machine charges early.
    Input-dependent builtin costs remain deferred in both paths. -/
def run (variant : BuiltinSemanticsVariant) (state : State)
    (remaining initial : ExBudget) (guard : Nat) : Result :=
  if remaining.canAfford (machineBudgetBound variant guard) then
    runDeferred variant state remaining initial guard
  else runWithMachineBudget variant state remaining initial guard []

/-- Bundled post-Conway costs: V3 uses E, V1/V2 use D. These are not cost
    coefficients loaded from network protocol parameters. -/
def execute (program : Program) (args : List Term) (cpu memory : Nat)
    (v3 : Bool) (guard : Nat := 100000) : Result :=
  let variant := if v3 then .defaultFunSemanticsVariantE else .defaultFunSemanticsVariantD
  let budget : ExBudget := ⟨⟨cpu⟩, ⟨memory⟩⟩
  let costs := semVarToCosts variant
  let startup := costs.startupCost
  if budget.canAfford startup then
    match program with
    | .Program _ body => run variant (initialState (applyParams body args))
        (budget - startup) budget guard
  else .budgetExhausted

/-- V3 requires unit; earlier ledger languages accept any successful return.
    `none` means analysis did not finish, not rejection. -/
def accepts (v3 : Bool) : Result → Option Bool
  | .success (.VCon .Unit) _ => some true
  | .success _ _ => some (!v3)
  | .error | .budgetExhausted => some false
  | .unfinished => none

/-- Sufficient even if one execution is unfinished: an old rejection or a new
    acceptance settles the implication. Unknown old execution is not vacuous. -/
def Preserved (v3 : Bool) (old new : Result) : Prop :=
  accepts v3 old = some false ∨ accepts v3 new = some true

def Regression (v3 : Bool) (old new : Result) : Prop :=
  accepts v3 old = some true ∧ accepts v3 new = some false

theorem preserved_of_rejected (v3 : Bool) (old new : Result)
    (rejected : accepts v3 old = some false) : Preserved v3 old new :=
  Or.inl rejected

theorem no_regression_of_rejected (v3 : Bool) (old new : Result)
    (rejected : accepts v3 old = some false) : ¬ Regression v3 old new := by
  intro regression
  have accepted := regression.1
  rw [rejected] at accepted
  contradiction

def preserved (v3 : Bool) (old new : Result) : Bool :=
  accepts v3 old == some false || accepts v3 new == some true

theorem no_regression_of_preserved (v3 : Bool) (old new : Result)
    (preserved : Preserved v3 old new) : ¬ Regression v3 old new := by
  rcases preserved with rejected | accepted
  · exact no_regression_of_rejected v3 old new rejected
  · intro regression
    have rejected := regression.2
    rw [accepted] at rejected
    contradiction

def regression (v3 : Bool) (old new : Result) : Bool :=
  accepts v3 old == some true && accepts v3 new == some false

end Equivalence.Acceptance
