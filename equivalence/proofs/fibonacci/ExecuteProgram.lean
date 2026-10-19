/-
Fibonacci, two scripts, without `#prep_uplc`: the theorems run the scripts with
`executeProgram` (Romain's draft: Romain's naive script vs Plinth 1.45).
Run: lake lean equivalence/proofs/fibonacci/ExecuteProgram.lean
-/
import CardanoLedgerApi.IsData.Class
import Blaster

namespace Equivalence.Proofs.Fibonacci.ExecuteProgram
open CardanoLedgerApi.IsData.Class
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.Utils
open PlutusCore.UPLC.CekMachine (cekExecuteProgram)

-- CLI Flag
def script1 : String := "Tests/Functions/Fibonacci/fibonacci_naive.flat"
def script2 : String := "equivalence/examples/fibonacci/Plinth_1.45.0.0_Unisay.cbor_hex"
def maxSteps : Nat := 1000

-- Step 1: Import the compiled UPLC code for both implementations
#import_uplc fibonacciNaiveRecursion PlutusV2 single_cbor_hex "Tests/Functions/Fibonacci/fibonacci_naive.flat"
#import_uplc fibonacciPlinth PlutusV3 single_cbor_hex "equivalence/examples/fibonacci/Plinth_1.45.0.0_Unisay.cbor_hex"

-- Step 2: Define the shape of the inputs
-- TOGET: from the blueprints?
def integerToParams (x : Integer) : List Term := [Term.Const $ Const.Integer x]

-- Helper to put somewhere?
def executeProgram (p : Program) (maxSteps : Nat) (args : List Term) :=
  fromFrameToInt $ cekExecuteProgram p args maxSteps


-- --- EASY/NAIVE EQUIVALENCE
-- -- Step 3: Equivalence between two implementations
-- theorem fibonacci_equiv :
--   ∀ (n : Integer),
--     executeProgram fibonacciNaiveRecursion.script maxSteps (integerToParams n)
--     = executeProgram fibonacciPlinth.script maxSteps (integerToParams n)
--   := by blaster (timeout: 20)

-- Step optional: Sanity check that sometimes the programe returns a value for that budget
theorem fibonacci_sometimes_output:
  ∃ (n r : Integer), (executeProgram fibonacciNaiveRecursion.script maxSteps (integerToParams n)) = some r := by blaster (timeout: 20)

--- MORE ROBUST EQUIVALENCE
-- Step 3: Same as before but one is more "optimized" than the other
theorem fibonacciPlinth_more_optimized_than_fibonacciNaiveRecursion :
  ∀ (n r1 r2 : Integer),
    executeProgram fibonacciNaiveRecursion.script maxSteps (integerToParams n) = some r1 →
    executeProgram fibonacciPlinth.script maxSteps (integerToParams n) = some r2 →
    r1 = r2 := by blaster (timeout: 20)

-- Step optional: Sanity check that sometimes the programe returns a value for that budget
theorem fibonacciPlinth_sometimes_output:
  ∃ (n r : Integer), (executeProgram fibonacciPlinth.script maxSteps (integerToParams n)) = some r := by blaster (timeout: 20)
theorem fibonacciNaiveRecursion_sometimes_output:
  ∃ (n r : Integer), (executeProgram fibonacciNaiveRecursion.script maxSteps (integerToParams n)) = some r := by blaster (timeout: 20)

end Equivalence.Proofs.Fibonacci.ExecuteProgram
