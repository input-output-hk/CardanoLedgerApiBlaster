import CardanoLedgerApi.V1

namespace Tests.Value

open PlutusCore.Data (Data)
open CardanoLedgerApi.V1.Value

/-! Guards for `valueOf`, which destructures its `Data` keys instead of applying
    equality at type `Data` (so that the SMT toolchain can translate it).  These
    exercise the flipped cases: a well-formed hit, a miss, an outer entry whose
    key is not a `Data.B`, an inner entry whose key is not a `Data.B`, and the
    malformed-payload cases.
-/

/-- Well-formed lookup hit. -/
example : valueOf "c" "t" [(Data.B "c", Data.Map [(Data.B "t", Data.I 7)])] = 7 := by rfl

/-- Well-formed lookup miss (currency symbol absent) still scans the tail. -/
example :
    valueOf "c" "t"
      [ (Data.B "a", Data.Map [(Data.B "t", Data.I 3)]),
        (Data.B "c", Data.Map [(Data.B "u", Data.I 5), (Data.B "t", Data.I 7)]) ] = 7 := by
  rfl

/-- Outer entry whose key is not a `Data.B` is skipped, not matched. -/
example :
    valueOf "c" "t"
      [ (Data.I 0, Data.Map [(Data.B "t", Data.I 3)]),
        (Data.B "c", Data.Map [(Data.B "t", Data.I 7)]) ] = 7 := by
  rfl

/-- Outer entry whose payload is not a `Data.Map` stops the scan and yields `0`,
    even though a matching entry follows. -/
example :
    valueOf "c" "t"
      [ (Data.B "a", Data.I 0),
        (Data.B "c", Data.Map [(Data.B "t", Data.I 7)]) ] = 0 := by
  rfl

/-- Inner entry whose key is not a `Data.B` is skipped, not matched. -/
example :
    valueOf "c" "t"
      [ (Data.B "c", Data.Map [(Data.I 0, Data.I 3), (Data.B "t", Data.I 7)]) ] = 7 := by
  rfl

/-- Inner key matches but the payload is not a `Data.I`: `0`, and the scan stops. -/
example :
    valueOf "c" "t"
      [ (Data.B "c", Data.Map [(Data.B "t", Data.B "x"), (Data.B "t", Data.I 7)]) ] = 0 := by
  rfl

-- The translatable definition agrees with the previous one in the kernel:
-- only the three standard axioms.
#print axioms CardanoLedgerApi.V1.Value.valueOf_eq_valueOfClassic

end Tests.Value
