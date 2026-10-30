import Equivalence.Acceptance

namespace Equivalence.Function

open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.Term (Program Term Const)
open Acceptance (Result)

/-- Unlike the upstream uncosted runner, retain exhaustion of the analysis limit. -/
def run (variant : PlutusCore.Default.BuiltinSemanticsVariant) (state : State)
    (steps : Nat) : Result :=
  match steps, state with
  | _, .Halt value => .success value ⟨⟨0⟩, ⟨0⟩⟩
  | _, .Error => .error
  | 0, _ => .unfinished
  | n + 1, _ => run variant (step variant state) n

def execute (program : Program) (args : List Term) (cpu memory : Nat)
    (v3 budgeted : Bool) (steps : Nat) : Result :=
  if budgeted then Acceptance.execute program args cpu memory v3 steps
  else
    let variant := if v3 then .defaultFunSemanticsVariantE else .defaultFunSemanticsVariantD
    match program with
    | .Program _ body => run variant (initialState (applyParams body args)) steps

mutual
  /-- The CEK model specializes Data lists/pairs internally. Compare their UPLC
      values rather than distinguishing those representation choices. -/
  def normalize : Const → Const
    | .ConstDataList xs => .ConstList (xs.map Const.Data)
    | .ConstPairDataList xs => .ConstList (xs.map fun (a, b) => .Pair (.Data a, .Data b))
    | .PairData (a, b) => .Pair (.Data a, .Data b)
    | .ConstList xs => .ConstList (normalizeList xs)
    | .Pair (a, b) => .Pair (normalize a, normalize b)
    | other => other

  def normalizeList : List Const → List Const
    | [] => []
    | x :: xs => normalize x :: normalizeList xs
end

/-- Ground constant results and evaluation errors are observable. Closures and
    constructor values require a future extensional comparison; they stay unknown.
    Budget/analysis exhaustion never establishes function equivalence. -/
def same : Result → Result → Option Bool
  | .success (.VCon left) _, .success (.VCon right) _ => some (normalize left == normalize right)
  | .error, .error => some true
  | .success _ _, .error | .error, .success _ _ => some false
  | _, _ => none

/-- A bounded observation deliberately merges every execution that fails to
    produce a constant: errors, other return values and exhausted limits. -/
def observation : Result → Option Const
  | .success (.VCon value) _ => some (normalize value)
  | _ => none

def boundedSame (left right : Result) : Bool :=
  observation left == observation right

/-- Preserve every observed OLD value; an absent OLD observation imposes no
    requirement on NEW. This permits additional completed executions. -/
def boundedPreserved (old new : Result) : Bool :=
  match observation old with
  | none => true
  | some value => observation new == some value

end Equivalence.Function
