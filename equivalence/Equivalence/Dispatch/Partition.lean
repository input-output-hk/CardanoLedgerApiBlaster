import Equivalence.Dispatch.Pattern

/-! Exhaustive proof partitions. Discovery supplies useful guards, but coverage
does not depend on discovering every branch or on pattern parameterization. -/

namespace Equivalence.Dispatch
open Lean Meta
open PlutusCore.Data (Data)

/-- First matching guard wins; the final index is the catch-all. -/
def select : List Bool → Nat → Bool
  | [], 0 => true
  | [], _ + 1 => false
  | first :: _, 0 => first
  | first :: rest, index + 1 => !first && select rest index

theorem select_covered (guards : List Bool) :
    ∃ index, index ≤ guards.length ∧ select guards index = true := by
  induction guards with
  | nil => exact ⟨0, Nat.le_refl _, rfl⟩
  | cons first rest ih =>
    cases first with
    | true => exact ⟨0, Nat.zero_le _, rfl⟩
    | false =>
      obtain ⟨index, bound, selected⟩ := ih
      exact ⟨index + 1, Nat.succ_le_succ bound, by simpa [select] using selected⟩

/-- Validity of every part establishes the original property, including when
    the discovered guards overlap, are contradictory, or omit entire Data kinds. -/
theorem of_partition {property : Prop} (guards : List Bool)
    (parts : ∀ index, index ≤ guards.length → select guards index = true → property) :
    property := by
  obtain ⟨index, bound, selected⟩ := select_covered guards
  exact parts index bound selected

/-- Compile a finite pattern into total facts. Arbitrary tails remain arbitrary;
    missing fields and mismatched Data constructors fail membership. -/
private partial def patternFacts (pattern : Pattern) (path : Path) : List Fact :=
  match pattern with
  | .any => []
  | .literal value => [.equal path value]
  | .integer => [.kind path .integer]
  | .bytes => [.kind path .bytes]
  | .constr tag fields exact =>
    (tag.map (fun tag => Fact.tag path tag)).toList ++
      [if exact then .length path .fields fields.length else .need path .fields fields.length] ++
      fields.zipIdx.flatMap (fun (field, index) => patternFacts field (path.child (.field index)))
  | .list items exact =>
    [if exact then .length path .items items.length else .need path .items items.length] ++
      items.zipIdx.flatMap (fun (item, index) => patternFacts item (path.child (.item index)))
  | .map entries exact =>
    [if exact then .length path .entries entries.length else .need path .entries entries.length] ++
      entries.zipIdx.flatMap (fun ((key, value), index) =>
        patternFacts key (path.child (.key index)) ++ patternFacts value (path.child (.value index)))

def Case.facts (candidate : Case) : List Fact :=
  patternFacts candidate.datum ⟨.datum, []⟩ ++
    patternFacts candidate.redeemer ⟨.redeemer, []⟩ ++ candidate.conditions

def Case.holds (candidate : Case) (datum redeemer : Data) : Bool :=
  candidate.facts.all (·.holds datum redeemer)

/-- Evaluate the ordered partition on concrete datum and redeemer values. -/
def partitionHolds (cases : Array Case) (index : Nat) (datum redeemer : Data) : Bool :=
  select (cases.toList.map (·.holds datum redeemer)) index

/-- Restrict the full context schema rather than treating parameterized search
    patterns as a proof of coverage. The extra part covers all unmatched inputs. -/
def partitionProposition (cases : Array Case) (index : Nat)
    (limits : ValidContext.Limits) (predicate : Expr) : MetaM Expr := do
  unless index ≤ cases.size do throwError "Dispatch partition index out of range"
  let restriction ← withLocalDeclD `datum (mkConst ``Data) fun datum =>
    withLocalDeclD `redeemer (mkConst ``Data) fun redeemer => do
      let guards := cases.toList.map fun candidate =>
        candidate.facts.foldr (fun fact rest =>
          mkApp2 (mkConst ``Bool.and)
            (mkApp3 (mkConst ``Fact.holds) (toExpr fact) datum redeemer) rest) (toExpr true)
      let guard := mkApp2 (mkConst ``select) (← mkListLit (mkConst ``Bool) guards) (toExpr index)
      mkLambdaFVars #[datum, redeemer] guard
  ValidContext.proposition limits predicate (restriction := some restriction)

end Equivalence.Dispatch
