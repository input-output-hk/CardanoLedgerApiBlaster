import PlutusCore.UPLC.PreProcess
import PlutusCore.UPLC.Utils

/-!
Input/output relations for a future equivalence CLI.

Run from the repository root:
  lake env lean equivalence/proofs/mappings/Relational.lean

The structures and argument builders below stand in for blueprint-generated code.
The three small UPLC programs are written directly as ASTs. They are pure payout
functions, NOT complete Cardano validators or a model of transaction validity.

Simulated user hints:
  B.rate = A.percent / 100       -- logical units, not integer division!
  B.metadata = arbitrary
  B.bonus = 0                   -- compare the original/legacy behavior
  output: integer <-> IData(integer)

Encoding of B.rate: fixed point with denominator 10000. Thus 25% corresponds to
0.25, encoded as 2500, and the wire relation is B.rateUnits = A.percent * 100.
No floating point or rounding is used in the input conversion. Both programs
floor the final payout using the evaluator's actual DivideInteger operation.

Proofs cover EVERY related input, not merely the displayed examples. Coverage
also proves every valid original input has a related valid extended input.
Unconstrained metadata is universally quantified. The new bonus feature is
restricted to zero only in the legacy equivalence relation.

Theorems use .exec (the original CEK execution), and prove a concrete successful
result within 200 steps. They therefore do not establish equality by comparing
two exhausted runs, or rely on the correctness of #prep_uplc's optimizer.
There is no Blaster tactic, sorry, or extra axiom in these proofs.
-/
namespace Equivalence.MappingExamples.Relational

open PlutusCore.Integer (Integer)
open PlutusCore.Data (Data)
open PlutusCore.UPLC.Term (Term Const BuiltinFun)
open PlutusCore.UPLC.PlutusScript (PlutusScript)
open PlutusCore.UPLC.CekMachine (State)
open PlutusCore.UPLC.Utils (fromFrameToInt)

/-! Simulated blueprint interfaces. -/

structure OriginalInput where
  amount : Integer
  percent : Integer

structure ExtendedInput where
  rateUnits : Integer
  amount : Integer
  metadata : Data
  bonus : Integer

def OriginalValid (a : OriginalInput) : Prop :=
  0 ≤ a.amount ∧ 0 ≤ a.percent ∧ a.percent ≤ 100

def ExtendedValid (b : ExtendedInput) : Prop :=
  0 ≤ b.amount ∧ 0 ≤ b.rateUnits ∧ b.rateUnits ≤ 10000 ∧ 0 ≤ b.bonus

/-- The relation is intentionally many-to-one: any metadata is allowed. -/
def Related (a : OriginalInput) (b : ExtendedInput) : Prop :=
  b.amount = a.amount ∧ b.rateUnits = a.percent * 100 ∧ b.bonus = 0

def adapt (a : OriginalInput) (metadata : Data) : ExtendedInput :=
  ⟨a.percent * 100, a.amount, metadata, 0⟩

theorem adapt_related (a : OriginalInput) (metadata : Data) : Related a (adapt a metadata) :=
  ⟨rfl, rfl, rfl⟩

theorem related_preserves_validity (a : OriginalInput) (b : ExtendedInput)
    (ha : OriginalValid a) (h : Related a b) : ExtendedValid b := by
  rcases ha with ⟨amount, percentLo, percentHi⟩
  rcases h with ⟨sameAmount, sameRate, legacy⟩
  dsimp [ExtendedValid]
  -- Omega needs the Integer alias unfolded to recognize Int arithmetic.
  simp only [Integer] at *
  omega

/-- Coverage is proved for every metadata value, not just one chosen default. -/
theorem covers_original (a : OriginalInput) (ha : OriginalValid a) (metadata : Data) :
    ∃ b, b.metadata = metadata ∧ ExtendedValid b ∧ Related a b := by
  exact ⟨adapt a metadata, rfl,
    related_preserves_validity a _ ha (adapt_related a metadata), adapt_related a metadata⟩

/-- The finer representation has valid rates with no whole-percent counterpart. -/
theorem finer_rate_has_no_original : ¬ ∃ p : Integer, p * 100 = 2550 := by
  change ¬ ∃ p : Int, p * 100 = 2550
  omega

/-! Actual UPLC programs and their argument builders. AST variables are zero-based. -/

private def binary (op : BuiltinFun) (x y : Term) : Term :=
  .Apply (.Apply (.Builtin op) x) y

private def int (n : Integer) : Term := .Const (.Integer n)

private def payout (amount rate : Term) (denominator : Integer) : Term :=
  binary .DivideInteger (binary .MultiplyInteger amount rate) (int denominator)

/-- A(amount, percent) = floor(amount * percent / 100), returning a builtin Integer. -/
def originalScript : PlutusScript :=
  { lang := .PlutusV3
    script := .Program (.Version 1 1 0)
      (.Lam (.Lam (payout (.Var 1) (.Var 0) 100))) }

/-- B(rate, amount, metadata) ignores metadata and returns its payout wrapped in Data.I. -/
def fractionalScript : PlutusScript :=
  { lang := .PlutusV3
    script := .Program (.Version 1 1 0)
      (.Lam (.Lam (.Lam (.Apply (.Builtin .IData) (payout (.Var 1) (.Var 2) 10000))))) }

/-- C(rate, amount, metadata, bonus) adds a new bonus feature to B. -/
def extendedScript : PlutusScript :=
  { lang := .PlutusV3
    script := .Program (.Version 1 1 0)
      (.Lam (.Lam (.Lam (.Lam (.Apply (.Builtin .IData)
        (binary .AddInteger (payout (.Var 2) (.Var 3) 10000) (.Var 0))))))) }

def originalArgs (a : OriginalInput) : List Term := [int a.amount, int a.percent]

def fractionalArgs (b : ExtendedInput) : List Term :=
  [int b.rateUnits, int b.amount, .Const (.Data b.metadata)]

def extendedArgs (b : ExtendedInput) : List Term := fractionalArgs b ++ [int b.bonus]

#prep_uplc mappingOriginal originalScript originalArgs 200
#prep_uplc mappingFractional fractionalScript fractionalArgs 200
#prep_uplc mappingExtended extendedScript extendedArgs 200

/-- Output correspondence: a builtin integer and Data.I carry the same payout.
    An error, exhausted run, or wrong result shape yields none. -/
def dataIntegerResult : State → Option Integer
  | .Halt (.VCon (.Data (.I n))) => some n
  | _ => none

def originalResult (a : OriginalInput) : Option Integer := fromFrameToInt (mappingOriginal.exec a)
def fractionalResult (b : ExtendedInput) : Option Integer := dataIntegerResult (mappingFractional.exec b)
def extendedResult (b : ExtendedInput) : Option Integer := dataIntegerResult (mappingExtended.exec b)

theorem original_evaluates (a : OriginalInput) :
    originalResult a = some (Int.fdiv (a.amount * a.percent) 100) := by rfl

theorem fractional_evaluates (b : ExtendedInput) :
    fractionalResult b = some (Int.fdiv (b.amount * b.rateUnits) 10000) := by rfl

theorem extended_evaluates (b : ExtendedInput) :
    extendedResult b = some (Int.fdiv (b.amount * b.rateUnits) 10000 + b.bonus) := by rfl

/-! 1. Percentage/fraction conversion, including rounding of the final payout. -/

theorem scale_preserves_payout (amount percent : Integer) :
    Int.fdiv (amount * (percent * 100)) 10000 = Int.fdiv (amount * percent) 100 := by
  rw [← Int.mul_assoc]
  exact Int.mul_fdiv_mul_of_pos_left (amount * percent) 100 (by decide : (0 : Int) < 100)

/-- Stronger than a valid-input-only claim: this algebraic equality holds for all integers. -/
theorem percentage_equivalence (a : OriginalInput) (b : ExtendedInput)
    (sameAmount : b.amount = a.amount) (sameRate : b.rateUnits = a.percent * 100) :
    originalResult a = fractionalResult b := by
  rw [original_evaluates, fractional_evaluates, sameAmount, sameRate, scale_preserves_payout]

/-! 2. Ignored extra input: equality for arbitrary pairs of metadata values. -/

theorem metadata_irrelevant (b : ExtendedInput) (d₁ d₂ : Data) :
    mappingExtended.exec { b with metadata := d₁ } =
      mappingExtended.exec { b with metadata := d₂ } := by rfl

theorem fractional_equivalence_any_metadata (a : OriginalInput) (metadata : Data) :
    originalResult a = fractionalResult (adapt a metadata) :=
  percentage_equivalence a _ rfl rfl

/-! 3. Additional behavior: equivalent on the legacy relation, not globally. -/

theorem legacy_equivalence (a : OriginalInput) (b : ExtendedInput) (h : Related a b) :
    originalResult a = extendedResult b := by
  rcases h with ⟨sameAmount, sameRate, legacy⟩
  rw [original_evaluates, extended_evaluates, sameAmount, sameRate, legacy,
    scale_preserves_payout, Int.add_zero]

/-- The new feature is described exactly, even outside the legacy subset. -/
theorem bonus_behavior (a : OriginalInput) (metadata : Data) (bonus : Integer) :
    extendedResult { adapt a metadata with bonus := bonus } =
      (originalResult a).map (fun n => n + bonus) := by
  rw [extended_evaluates, original_evaluates]
  simp only [adapt, scale_preserves_payout, Option.map_some]

/-- No proof can recover arbitrary ignored metadata from the original input alone. -/
theorem projection_loses_metadata :
    ∃ b₁ b₂ : ExtendedInput,
      b₁ ≠ b₂ ∧ Related ⟨1000, 25⟩ b₁ ∧ Related ⟨1000, 25⟩ b₂ := by
  refine ⟨adapt ⟨1000, 25⟩ (.I 0), adapt ⟨1000, 25⟩ (.I 1), ?_,
    adapt_related _ _, adapt_related _ _⟩
  intro h
  have bad : Data.I 0 = Data.I 1 := congrArg ExtendedInput.metadata h
  cases bad

/-! Checked examples and negative controls. A wrong mapping must change the answer. -/

example : originalResult ⟨1000, 25⟩ = some 250 := rfl
example : fractionalResult (adapt ⟨1000, 25⟩ (.B "ignored")) = some 250 := rfl
example : originalResult ⟨199, 50⟩ = some 99 := rfl
example : fractionalResult (adapt ⟨199, 50⟩ (.Constr 9 [])) = some 99 := rfl
example : originalResult ⟨1000, 0⟩ = some 0 := rfl
example : fractionalResult (adapt ⟨1000, 100⟩ (.List [])) = some 1000 := rfl

theorem missing_scale_is_wrong :
    originalResult ⟨1000, 25⟩ ≠ fractionalResult ⟨25, 1000, .I 0, 0⟩ := by decide

theorem enabled_bonus_is_not_equivalent :
    originalResult ⟨1000, 25⟩ ≠
      extendedResult { adapt ⟨1000, 25⟩ (.I 0) with bonus := 5 } := by decide

-- Both inputs of the new-feature counterexample are within their declared domains.
example : OriginalValid ⟨1000, 25⟩ := by unfold OriginalValid; decide
example : ExtendedValid { adapt ⟨1000, 25⟩ (.I 0) with bonus := 5 } := by
  unfold ExtendedValid adapt
  decide

-- Treating the logical conversion as integer division loses the fractional rate.
example : (25 : Integer) / 100 = 0 := rfl

#eval originalResult ⟨1000, 25⟩ -- some 250
#eval fractionalResult (adapt ⟨1000, 25⟩ (.B "anything")) -- some 250
#eval extendedResult { adapt ⟨1000, 25⟩ (.I 0) with bonus := 5 } -- some 255
#eval fractionalResult ⟨25, 1000, .I 0, 0⟩ -- some 2: missing conversion

-- Inspect trust dependencies: standard Lean axioms only; no sorryAx or blasterProven.
#print axioms covers_original
#print axioms original_evaluates
#print axioms fractional_evaluates
#print axioms extended_evaluates
#print axioms percentage_equivalence
#print axioms metadata_irrelevant
#print axioms legacy_equivalence
#print axioms bonus_behavior
#print axioms projection_loses_metadata
#print axioms missing_scale_is_wrong
#print axioms enabled_bonus_is_not_equivalent

end Equivalence.MappingExamples.Relational
