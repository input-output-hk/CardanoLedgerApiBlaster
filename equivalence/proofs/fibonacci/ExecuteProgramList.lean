/-
Fibonacci, a list of scripts, without `#prep_uplc`: the theorems run the scripts with
`executeProgram` (otherwise as `FibonacciList.lean`; slower).
Run: lake lean equivalence/proofs/fibonacci/ExecuteProgramList.lean
-/
import CardanoLedgerApi.IsData.Class
import Blaster

namespace Equivalence.Proofs.Fibonacci.ExecuteProgramList
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.Utils
open PlutusCore.UPLC.CekMachine (cekExecuteProgram)

set_option warn.sorry false

def maxSteps : Nat := 1000

def integerToParams (x : Integer) : List Term := [Term.Const $ Const.Integer x]

def executeProgram (p : Program) (maxSteps : Nat) (args : List Term) :=
  fromFrameToInt $ cekExecuteProgram p args maxSteps

-- Every Fibonacci script: Romain's naive one and all of `equivalence/examples/fibonacci/`.
#import_uplc naiveScript               PlutusV3 single_cbor_hex "Tests/Functions/Fibonacci/fibonacci_naive.flat"
#import_uplc aikenPrepackedScript      PlutusV3 single_cbor_hex "equivalence/examples/fibonacci/Aiken_1.1.19_KtorZ_prepacked.cbor_hex"
#import_uplc aikenTailrecScript        PlutusV3 single_cbor_hex "equivalence/examples/fibonacci/Aiken_1.1.19_KtorZ_tailrec.cbor_hex"
#import_uplc opshinScript              PlutusV3 single_cbor_hex "equivalence/examples/fibonacci/OpShin_1.0.0_nielstron.cbor_hex"
#import_uplc plinth145Script           PlutusV3 single_cbor_hex "equivalence/examples/fibonacci/Plinth_1.45.0.0_Unisay.cbor_hex"
#import_uplc plinth161Script           PlutusV3 single_cbor_hex "equivalence/examples/fibonacci/Plinth_1.61.0.0_Unisay.cbor_hex"
#import_uplc plinth164Script           PlutusV3 single_cbor_hex "equivalence/examples/fibonacci/Plinth_1.64.0.0_Unisay.cbor_hex"
#import_uplc plinth165Script           PlutusV3 single_cbor_hex "equivalence/examples/fibonacci/Plinth_1.65.0.0_Unisay.cbor_hex"
#import_uplc plinth167Script           PlutusV3 single_cbor_hex "equivalence/examples/fibonacci/Plinth_1.67.0.0_Unisay.cbor_hex"
#import_uplc plutarchExbudgetScript    PlutusV3 single_cbor_hex "equivalence/examples/fibonacci/Plutarch_1.11.0_SeungheonOh_exbudget.cbor_hex"
#import_uplc plutarchPrepackedScript   PlutusV3 single_cbor_hex "equivalence/examples/fibonacci/Plutarch_1.11.0_SeungheonOh_prepacked.cbor_hex"
#import_uplc plutarchSizeScript        PlutusV3 single_cbor_hex "equivalence/examples/fibonacci/Plutarch_1.11.0_SeungheonOh_size.cbor_hex"
#import_uplc scalus0121PrepackedScript PlutusV3 single_cbor_hex "equivalence/examples/fibonacci/Scalus_0.12.1_nau_prepacked.cbor_hex"
#import_uplc scalus0121Script          PlutusV3 single_cbor_hex "equivalence/examples/fibonacci/Scalus_0.12.1_Unisay.cbor_hex"
#import_uplc scalus0160Script          PlutusV3 single_cbor_hex "equivalence/examples/fibonacci/Scalus_0.16.0_Unisay.cbor_hex"
#import_uplc scalus0160PrepackedScript PlutusV3 single_cbor_hex "equivalence/examples/fibonacci/Scalus_0.16.0_Unisay_prepacked.cbor_hex"
#import_uplc scalus0170Script          PlutusV3 single_cbor_hex "equivalence/examples/fibonacci/Scalus_0.17.0_Unisay.cbor_hex"
#import_uplc scalus0182Script          PlutusV3 single_cbor_hex "equivalence/examples/fibonacci/Scalus_0.18.2_Unisay.cbor_hex"

/-- The scripts to compare. -/
def scripts : List Program := [
  naiveScript.script,
  aikenTailrecScript.script,
  opshinScript.script,        -- returns on fewer inputs (needs more steps), e.g. not n = 5
  plinth145Script.script,
  plutarchExbudgetScript.script,
  plutarchSizeScript.script,
  -- Same bytes as plutarchSize
  scalus0121Script.script,
  scalus0160Script.script,
  scalus0170Script.script,
  -- `all_agree` fails with "Inductive datatype with instance parameters
  -- not supported: BitVec": they look results up in a byte table, which Blaster can't
  -- handle (scalus0160Prepacked has the same bytes as scalus0121Prepacked):
  -- aikenPrepackedScript.script,
  -- plutarchPrepackedScript.script,
  -- scalus0121PrepackedScript.script,
  -- scalus0160PrepackedScript.script,
  -- Never finish: they branch with `case` on a builtin Bool, which Blaster
  -- can't simplify (1.64 has the same bytes as 1.61, 1.67 the same as 1.65):
  -- plinth161Script.script,
  -- plinth164Script.script,
  -- plinth165Script.script,
  -- plinth167Script.script,
  -- scalus0182Script.script,
]

/-- Wherever both `f` and `g` return a result, it is the same result. -/
def Agree (f g : Program) : Prop :=
  ∀ (n r1 r2 : Integer),
    executeProgram f maxSteps (integerToParams n) = some r1 →
    executeProgram g maxSteps (integerToParams n) = some r2 →
    r1 = r2

def AgreesWithAll (f : Program) : List Program → Prop
  | [] => True
  | g :: rest => Agree f g ∧ AgreesWithAll f rest

/-- `Agree` holds between every two scripts of the list. -/
-- this might change when we do mapping between inputs/output
-- because we might need to use different style of mappings 
-- eg: (s1 -> s2), (s1 -> s3) ... (s1 -> sn)
-- eg2: (s1 -> s2), (s2 -> s3) ... (sn-1 -> sn)
-- etc
def AllAgree : List Program → Prop
  | [] => True
  | f :: rest => AgreesWithAll f rest ∧ AllAgree rest

/-- Every script of the list returns a result on input `n`. -/
def AllReturn (n : Integer) : List Program → Prop
  | [] => True
  | f :: rest => (∃ r, executeProgram f maxSteps (integerToParams n) = some r) ∧ AllReturn n rest

/-- 1. Every two scripts agree wherever both return a result. -/
theorem all_agree : AllAgree scripts := by blaster (timeout: 60)

/-- 2. Not vacuous: on some input all scripts return a result, so (1) compares something. -/
theorem all_return : ∃ n, AllReturn n scripts := by
  -- Blaster rejects this `∃` over the recursive `AllReturn`, so spell it out first.
  simp only [scripts, AllReturn, and_true]
  blaster (timeout: 60)

end Equivalence.Proofs.Fibonacci.ExecuteProgramList
