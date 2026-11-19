/-
ECD (Euclid's GCD).
Every two scripts of `scripts` are compared.
Run: lake lean equivalence/proofs/ecd/EcdList.lean
-/
import CardanoLedgerApi.IsData.Class
import Blaster

namespace Equivalence.Proofs.Ecd.EcdList
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.Utils
open PlutusCore.UPLC.CekMachine (State)

set_option warn.sorry false

/-- How the input is passed to a script: the scripts take two UPLC integers, `(con integer a)`
and `(con integer b)`. `#prep_uplc` applies each script to `toParams a b` for symbolic `a`
and `b`. -/
def toParams (a b : Integer) : List Term :=
  [Term.Const $ Const.Integer a, Term.Const $ Const.Integer b]

-- Every script of `equivalence/examples/ecd/`.
#import_uplc plinth145Script PlutusV3 single_cbor_hex "equivalence/examples/ecd/Plinth_1.45.0.0_Unisay.cbor_hex"
#import_uplc plinth161Script PlutusV3 single_cbor_hex "equivalence/examples/ecd/Plinth_1.61.0.0_Unisay.cbor_hex"
#import_uplc plinth164Script PlutusV3 single_cbor_hex "equivalence/examples/ecd/Plinth_1.64.0.0_Unisay.cbor_hex"
#import_uplc plinth165Script PlutusV3 single_cbor_hex "equivalence/examples/ecd/Plinth_1.65.0.0_Unisay.cbor_hex"
#import_uplc plinth167Script PlutusV3 single_cbor_hex "equivalence/examples/ecd/Plinth_1.67.0.0_Unisay.cbor_hex"

-- `#prep_uplc x xScript toParams 1000` defines `x.prop : Integer → Integer → State`: the script
-- `xScript` as a Lean function of its input. `x.prop a b` is the final state of the CEK machine
-- (the UPLC evaluator) after running the script on that input, with at most 1000 steps:
--   `.Halt v`: the script finished with the value `v` (here an integer);
--   `.Error`: the script failed, or it ran out of steps.
-- `fromFrameToInt` reads it as a result: `some r` for `.Halt` with the integer `r`, `none`
-- otherwise. `#prep_uplc` runs the script on a symbolic input and Blaster simplifies the
-- result once here, so the theorems below don't redo it. This is the slow step, so only
-- the scripts used in `scripts` are prepared; see there why the others are left out.
#prep_uplc plinth145 plinth145Script toParams 1000
-- #prep_uplc plinth161 plinth161Script toParams 1000
-- #prep_uplc plinth164 plinth164Script toParams 1000
-- #prep_uplc plinth165 plinth165Script toParams 1000
-- #prep_uplc plinth167 plinth167Script toParams 1000

/-- The scripts to compare, each `x.prop` of a prepared script `x`: a function from the input `a b` to
the machine's final state (see the `#prep_uplc` lines). To add one, uncomment its
`#prep_uplc` line above too. `noncomputable`: `x.prop` is a term for proofs, Lean doesn't
compile it to run (`x.exec` is the runnable version). -/
noncomputable def scripts : List (Integer → Integer → State) := [
  plinth145.prop,
  -- Never finish preparing: they branch with `case` on a builtin result, which Blaster
  -- can't simplify:
  -- plinth161.prop,
  -- plinth164.prop,
  -- plinth165.prop,  -- same bytes as plinth164
  -- plinth167.prop,  -- same bytes as plinth161
]

/-- Wherever both `f` and `g` return a result, it is the same result: for every input `a b`, if
`f` returns `r1` and `g` returns `r2` (`fromFrameToInt`, see the `#prep_uplc` lines), then
`r1 = r2`. Inputs on which one of them fails or runs out of steps are not compared. -/
def Agree (f g : Integer → Integer → State) : Prop :=
  ∀ (a b r1 r2 : Integer),
    fromFrameToInt (f a b) = some r1 →
    fromFrameToInt (g a b) = some r2 →
    r1 = r2

/-- `f` agrees (`Agree`) with every script of the list. -/
def AgreesWithAll (f : Integer → Integer → State) : List (Integer → Integer → State) → Prop
  | [] => True
  | g :: rest => Agree f g ∧ AgreesWithAll f rest

/-- `Agree` holds between every two scripts of the list: `AllAgree [a, b, c]` is
`(Agree a b ∧ Agree a c) ∧ Agree b c`. -/
-- this might change when we do mapping between inputs/output
-- because we might need to use different style of mappings 
-- eg: (s1 -> s2), (s1 -> s3) ... (s1 -> sn)
-- eg2: (s1 -> s2), (s2 -> s3) ... (sn-1 -> sn)
-- etc
def AllAgree : List (Integer → Integer → State) → Prop
  | [] => True
  | f :: rest => AgreesWithAll f rest ∧ AllAgree rest

/-- Every script of the list returns a result on input `a b`. -/
def AllReturn (a b : Integer) : List (Integer → Integer → State) → Prop
  | [] => True
  | f :: rest => (∃ r, fromFrameToInt (f a b) = some r) ∧ AllReturn a b rest

/-- 1. Every two scripts agree wherever both return a result. -/
theorem all_agree : AllAgree scripts := by blaster (timeout: 60)

/-- 2. Not vacuous: on some input all scripts return a result, so (1) compares something. -/
theorem all_return : ∃ a b, AllReturn a b scripts := by
  -- Blaster rejects this `∃` over the recursive `AllReturn`, so spell it out first.
  simp only [scripts, AllReturn, and_true]
  blaster (timeout: 60)

end Equivalence.Proofs.Ecd.EcdList
