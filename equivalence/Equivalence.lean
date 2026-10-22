import PlutusCore.UPLC

namespace Equivalence

open PlutusCore.UPLC.CekMachine (State step initialState applyParams)
open PlutusCore.UPLC.CekValue (CekValue)
open PlutusCore.UPLC.PlutusScript (PlutusScript)
open PlutusCore.UPLC.Term (Term Const Program)

/-- Unlike the upstream `runSteps`, leave an unfinished state intact at zero fuel.
    The CEK transition function and its builtin semantics are unchanged. -/
def runSteps (state : State) (fuel : Nat) : State :=
  match fuel, state with
  | _, .Halt _ => state
  | _, .Error => state
  | 0, _ => state
  | n + 1, _ => runSteps (step default state) n

def execute (program : Program) (args : List Term) (fuel : Nat) : State :=
  match program with
  | .Program _ body => runSteps (initialState (applyParams body args)) fuel

/-- Only terminal states have an observable result. Fuel exhaustion is not an error. -/
inductive Outcome where
  | success : CekValue → Outcome
  | failure : Outcome
deriving Repr

def observe : State → Option Outcome
  | .Halt value => some (.success value)
  | .Error => some .failure
  | _ => none

/-- A caller-supplied relation compares successful values; errors match errors. -/
def OutputEquiv (values : CekValue → CekValue → Prop) : Outcome → Outcome → Prop
  | .success x, .success y => values x y
  | .failure, .failure => True
  | _, _ => False

/-- Integer functions must actually return integers, even when both return the same
    unexpected value. Validators can instead supply a relation ignoring successful values. -/
def IntegerValues : CekValue → CekValue → Prop
  | .VCon (.Integer x), .VCon (.Integer y) => x = y
  | _, _ => False

/-- A finite run witnesses a semantic outcome. Fuel is existential and independent
    on each side: it is not part of the input or output equivalence criterion. -/
def Evaluates (script : PlutusScript) (args : List Term) (result : Outcome) : Prop :=
  ∃ fuel, observe (execute script.script args fuel) = some result

/-- Terminating equivalence on related inputs. This prototype requires termination
    of both programs; it does not establish equivalence of divergent programs. -/
def Equivalent {α β : Type} (inputs : α → β → Prop)
    (leftArgs : α → List Term) (rightArgs : β → List Term)
    (values : CekValue → CekValue → Prop) (left right : PlutusScript) : Prop :=
  ∀ x y, inputs x y → ∃ a b,
    Evaluates left (leftArgs x) a ∧ Evaluates right (rightArgs y) b ∧
    OutputEquiv values a b

/-- The sufficient obligation given to Blaster for chosen, independent fuel limits.
    Requiring terminal results prevents two exhausted runs from proving equivalence.
    Falsifying this obligation alone is inconclusive: use `RunsMismatch` to establish
    a genuine counterexample with two completed executions. -/
def RunsEquivalent (values : CekValue → CekValue → Prop) (left right : State) : Prop :=
  match observe left, observe right with
  | some a, some b => OutputEquiv values a b
  | _, _ => False

/-- A semantic mismatch requires two terminal outcomes. Exhaustion cannot witness one.
    Falsify `∀ x y, inputs x y → ¬ RunsMismatch values (left x) (right y)` with Blaster
    to establish that a related input pair produces inequivalent outputs. -/
def RunsMismatch (values : CekValue → CekValue → Prop) (left right : State) : Prop :=
  match observe left, observe right with
  | some a, some b => ¬ OutputEquiv values a b
  | _, _ => False

theorem equivalent_of_runs {α β : Type} (inputs : α → β → Prop)
    (leftArgs : α → List Term) (rightArgs : β → List Term)
    (values : CekValue → CekValue → Prop) (left right : PlutusScript)
    (leftFuel rightFuel : Nat)
    (checked : ∀ x y, inputs x y → RunsEquivalent values
      (execute left.script (leftArgs x) leftFuel)
      (execute right.script (rightArgs y) rightFuel)) :
    Equivalent inputs leftArgs rightArgs values left right := by
  intro x y related
  have h := checked x y related
  unfold RunsEquivalent at h
  cases hl : observe (execute left.script (leftArgs x) leftFuel) with
  | none => simp [hl] at h
  | some a =>
    cases hr : observe (execute right.script (rightArgs y) rightFuel) with
    | none => simp [hl, hr] at h
    | some b =>
      exact ⟨a, b, ⟨leftFuel, hl⟩, ⟨rightFuel, hr⟩, by simpa [hl, hr] using h⟩

inductive Verdict where
  | equivalent
  | inequivalent
  | inconclusive
deriving Repr, BEq, DecidableEq

/-- Concrete diagnostic. Only two completed, differing results yield inequivalent. -/
def compareRuns (values : CekValue → CekValue → Bool) (left right : State) : Verdict :=
  match observe left, observe right with
  | some (.success a), some (.success b) =>
    if values a b then .equivalent else .inequivalent
  | some .failure, some .failure => .equivalent
  | some _, some _ => .inequivalent
  | _, _ => .inconclusive

def integerValues : CekValue → CekValue → Bool
  | .VCon (.Integer x), .VCon (.Integer y) => x == y
  | _, _ => false

end Equivalence
