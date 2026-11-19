/-
Factorial (optimized and naive recursion).
Every two scripts of `scripts` are compared.
Run: lake lean equivalence/proofs/factorial/FactorialList.lean
-/
import CardanoLedgerApi.IsData.Class
import Blaster

namespace Equivalence.Proofs.Factorial.FactorialList
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.Utils
open PlutusCore.UPLC.CekMachine (State)

set_option warn.sorry false

/-- How the input is passed to a script: the scripts take one UPLC integer, `(con integer x)`.
`#prep_uplc` applies each script to `toParams x` for a symbolic `x`. -/
def toParams (x : Integer) : List Term := [Term.Const $ Const.Integer x]

-- Every script of `equivalence/examples/factorial/`.
#import_uplc plutarchExbudgetScript PlutusV3 single_cbor_hex "equivalence/examples/factorial/Plutarch_1.11.0_SeungheonOh_exbudget.cbor_hex"
#import_uplc plutarchSizeScript     PlutusV3 single_cbor_hex "equivalence/examples/factorial/Plutarch_1.11.0_SeungheonOh_size.cbor_hex"
#import_uplc scalus0121Script       PlutusV3 single_cbor_hex "equivalence/examples/factorial/Scalus_0.12.1_Unisay.cbor_hex"
#import_uplc scalus0160Script       PlutusV3 single_cbor_hex "equivalence/examples/factorial/Scalus_0.16.0_Unisay.cbor_hex"
#import_uplc scalus0170Script       PlutusV3 single_cbor_hex "equivalence/examples/factorial/Scalus_0.17.0_Unisay.cbor_hex"

-- Every script of `equivalence/examples/factorial_naive_recursion/` (naive recursion).
#import_uplc naiveOpshinScript      PlutusV3 single_cbor_hex "equivalence/examples/factorial_naive_recursion/OpShin_1.0.0_nielstron.cbor_hex"
#import_uplc naivePebbleScript      PlutusV3 single_cbor_hex "equivalence/examples/factorial_naive_recursion/Pebble_0.1.2_michele-nuzzi.cbor_hex"
#import_uplc naivePlinth145Script   PlutusV3 single_cbor_hex "equivalence/examples/factorial_naive_recursion/Plinth_1.45.0.0_Unisay.cbor_hex"
#import_uplc naivePlinth161Script   PlutusV3 single_cbor_hex "equivalence/examples/factorial_naive_recursion/Plinth_1.61.0.0_Unisay.cbor_hex"
#import_uplc naivePlinth164Script   PlutusV3 single_cbor_hex "equivalence/examples/factorial_naive_recursion/Plinth_1.64.0.0_Unisay.cbor_hex"
#import_uplc naivePlinth165Script   PlutusV3 single_cbor_hex "equivalence/examples/factorial_naive_recursion/Plinth_1.65.0.0_Unisay.cbor_hex"
#import_uplc naivePlinth167Script   PlutusV3 single_cbor_hex "equivalence/examples/factorial_naive_recursion/Plinth_1.67.0.0_Unisay.cbor_hex"
#import_uplc naivePlutarchScript    PlutusV3 single_cbor_hex "equivalence/examples/factorial_naive_recursion/Plutarch_1.11.0_SeungheonOh.cbor_hex"
#import_uplc naiveScalus0121Script  PlutusV3 single_cbor_hex "equivalence/examples/factorial_naive_recursion/Scalus_0.12.1_Unisay.cbor_hex"
#import_uplc naiveScalus0160Script  PlutusV3 single_cbor_hex "equivalence/examples/factorial_naive_recursion/Scalus_0.16.0_Unisay.cbor_hex"
#import_uplc naiveScalus0170Script  PlutusV3 single_cbor_hex "equivalence/examples/factorial_naive_recursion/Scalus_0.17.0_Unisay.cbor_hex"
#import_uplc naiveScalus0182Script  PlutusV3 single_cbor_hex "equivalence/examples/factorial_naive_recursion/Scalus_0.18.2_Unisay.cbor_hex"

-- `#prep_uplc x xScript toParams 1000` defines `x.prop : Integer → State`: the script
-- `xScript` as a Lean function of its input. `x.prop n` is the final state of the CEK machine
-- (the UPLC evaluator) after running the script on that input, with at most 1000 steps:
--   `.Halt v`: the script finished with the value `v` (here an integer);
--   `.Error`: the script failed, or it ran out of steps.
-- `fromFrameToInt` reads it as a result: `some r` for `.Halt` with the integer `r`, `none`
-- otherwise. `#prep_uplc` runs the script on a symbolic input and Blaster simplifies the
-- result once here, so the theorems below don't redo it. This is the slow step, so only
-- the scripts used in `scripts` are prepared; see there why the others are left out.
#prep_uplc plutarchExbudget plutarchExbudgetScript toParams 1000
#prep_uplc plutarchSize     plutarchSizeScript     toParams 1000
#prep_uplc scalus0121       scalus0121Script       toParams 1000
#prep_uplc scalus0160       scalus0160Script       toParams 1000
#prep_uplc scalus0170       scalus0170Script       toParams 1000
#prep_uplc naiveOpshin     naiveOpshinScript     toParams 1000
#prep_uplc naivePebble     naivePebbleScript     toParams 1000
#prep_uplc naivePlinth145  naivePlinth145Script  toParams 1000
-- #prep_uplc naivePlinth161  naivePlinth161Script  toParams 1000
-- #prep_uplc naivePlinth164  naivePlinth164Script  toParams 1000
-- #prep_uplc naivePlinth165  naivePlinth165Script  toParams 1000
-- #prep_uplc naivePlinth167  naivePlinth167Script  toParams 1000
#prep_uplc naivePlutarch   naivePlutarchScript   toParams 1000
#prep_uplc naiveScalus0121 naiveScalus0121Script toParams 1000
#prep_uplc naiveScalus0160 naiveScalus0160Script toParams 1000
-- #prep_uplc naiveScalus0170 naiveScalus0170Script toParams 1000
-- #prep_uplc naiveScalus0182 naiveScalus0182Script toParams 1000

/-- The scripts to compare, each `x.prop` of a prepared script `x`: a function from the input `n` to
the machine's final state (see the `#prep_uplc` lines). To add one, uncomment its
`#prep_uplc` line above too. `noncomputable`: `x.prop` is a term for proofs, Lean doesn't
compile it to run (`x.exec` is the runnable version). -/
noncomputable def scripts : List (Integer → State) := [
  plutarchExbudget.prop,
  plutarchSize.prop,
  scalus0121.prop,  -- same bytes as plutarchSize
  scalus0160.prop,  -- same bytes as plutarchSize
  scalus0170.prop,  -- same bytes as plutarchSize
  -- Naive recursion (`equivalence/examples/factorial_naive_recursion/`):
  naiveOpshin.prop,
  naivePebble.prop,
  naivePlinth145.prop,
  naivePlutarch.prop,
  naiveScalus0121.prop,
  naiveScalus0160.prop,
  -- Never finish preparing: they branch with `case` on a builtin result, which Blaster
  -- can't simplify:
  -- naivePlinth161.prop,
  -- naivePlinth164.prop,  -- same bytes as naivePlinth161
  -- naivePlinth165.prop,  -- same bytes as naivePlinth161
  -- naivePlinth167.prop,  -- same bytes as naivePlinth161
  -- naiveScalus0170.prop,
  -- naiveScalus0182.prop,  -- same bytes as naiveScalus0170
]

/-- Wherever both `f` and `g` return a result, it is the same result: for every input `n`, if
`f` returns `r1` and `g` returns `r2` (`fromFrameToInt`, see the `#prep_uplc` lines), then
`r1 = r2`. Inputs on which one of them fails or runs out of steps are not compared. -/
def Agree (f g : Integer → State) : Prop :=
  ∀ (n r1 r2 : Integer),
    fromFrameToInt (f n) = some r1 →
    fromFrameToInt (g n) = some r2 →
    r1 = r2

/-- `f` agrees (`Agree`) with every script of the list. -/
def AgreesWithAll (f : Integer → State) : List (Integer → State) → Prop
  | [] => True
  | g :: rest => Agree f g ∧ AgreesWithAll f rest

/-- `Agree` holds between every two scripts of the list: `AllAgree [a, b, c]` is
`(Agree a b ∧ Agree a c) ∧ Agree b c`. -/
-- this might change when we do mapping between inputs/output
-- because we might need to use different style of mappings 
-- eg: (s1 -> s2), (s1 -> s3) ... (s1 -> sn)
-- eg2: (s1 -> s2), (s2 -> s3) ... (sn-1 -> sn)
-- etc
def AllAgree : List (Integer → State) → Prop
  | [] => True
  | f :: rest => AgreesWithAll f rest ∧ AllAgree rest

/-- Every script of the list returns a result on input `n`. -/
def AllReturn (n : Integer) : List (Integer → State) → Prop
  | [] => True
  | f :: rest => (∃ r, fromFrameToInt (f n) = some r) ∧ AllReturn n rest

/-- 1. Every two scripts agree wherever both return a result. -/
theorem all_agree : AllAgree scripts := by blaster (timeout: 60)

/-- 2. Not vacuous: on some input all scripts return a result, so (1) compares something. -/
theorem all_return : ∃ n, AllReturn n scripts := by
  -- Blaster rejects this `∃` over the recursive `AllReturn`, so spell it out first.
  simp only [scripts, AllReturn, and_true]
  blaster (timeout: 60)

end Equivalence.Proofs.Factorial.FactorialList
