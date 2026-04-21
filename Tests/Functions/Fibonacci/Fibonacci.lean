import CardanoLedgerApi.IsData.Class
import Blaster

namespace Tests.Functions.Fibonacci
open CardanoLedgerApi.IsData.Class
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.Utils

/-! # Test cases with Valid result expected -/

set_option warn.sorry false

#import_uplc fibonacciNaiveRecursion PlutusV2 single_cbor_hex "Tests/Functions/Fibonacci/fibonacci_native.flat"

#import_uplc fibonacciSeungheonOhSize PlutusV2 single_cbor_hex "Tests/Functions/Fibonacci/fibonacci_size.flat"

def integerToParams (x : Integer) : List Term := [Term.Const $ Const.Integer x]

#prep_uplc compiledSeungheonOhSize fibonacciSeungheonOhSize integerToParams 4000

#prep_uplc compiledNaiveRecursion fibonacciNaiveRecursion integerToParams 4000

-- Fibonacci 0 = 0
#blaster [ (fromFrameToInt $ compiledSeungheonOhSize.prop 0) = some 0]

-- Fibonacci 1 = 1
#blaster [ (fromFrameToInt $ compiledSeungheonOhSize.prop 1) = some 1]

-- ∀ (n : Integer), n > 1 → Fibonacci n = Fibonacci (n - 1) + Fibonacci (n - 2)
theorem fibonacci_sum :
  ∀ (n r1 r2 r3 : Integer), n > 1 →
    (fromFrameToInt $ compiledSeungheonOhSize.prop n) = some r1 →
    (fromFrameToInt $ compiledSeungheonOhSize.prop (n - 1)) = some r2 →
    (fromFrameToInt $ compiledSeungheonOhSize.prop (n - 2)) = some r3 →
    r1 = r2 + r3 := by blaster

-- Equivalence between two implementations
theorem fibonacci_equiv :
  ∀ (n : Integer),
    (fromFrameToInt $ compiledNaiveRecursion.prop n) = (fromFrameToInt $ compiledSeungheonOhSize.prop n) := by blaster

end Tests.Functions.Fibonacci
