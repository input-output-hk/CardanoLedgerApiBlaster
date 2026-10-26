import PlutusCore.UPLC

namespace Equivalence.Acceptance

open PlutusCore.Default
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue (CekValue)
open PlutusCore.UPLC.ExBudget (ExBudget)
open PlutusCore.UPLC.Term (Program Term)

inductive Result where
  | success : CekValue → ExBudget → Result
  | error
  | budgetExhausted
  | unfinished
deriving Repr

/-- Keep the analysis guard distinct from ledger budget exhaustion. -/
def run (variant : BuiltinSemanticsVariant) (state : State)
    (remaining initial : ExBudget) (guard : Nat) : Result :=
  match EvaluationResult.ofCostedRun remaining (runStepsWithCost variant state guard) with
  | .Success value spent => .success value (initial - (remaining - spent))
  | .EvaluationError => .error
  | .BudgetExhausted _ => .budgetExhausted
  | .StepLimitReached _ => .unfinished

/-- Bundled post-Conway costs: V3 uses E, V1/V2 use D. These are not cost
    coefficients loaded from network protocol parameters. -/
def execute (program : Program) (args : List Term) (cpu memory : Nat)
    (v3 : Bool) (guard : Nat := 100000) : Result :=
  let variant := if v3 then .defaultFunSemanticsVariantE else .defaultFunSemanticsVariantD
  let budget : ExBudget := ⟨⟨cpu⟩, ⟨memory⟩⟩
  let startup := (semVarToCosts variant).startupCost
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

def preserved (v3 : Bool) (old new : Result) : Bool :=
  accepts v3 old == some false || accepts v3 new == some true

def regression (v3 : Bool) (old new : Result) : Bool :=
  accepts v3 old == some true && accepts v3 new == some false

end Equivalence.Acceptance
