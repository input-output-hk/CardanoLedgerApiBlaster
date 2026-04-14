import CardanoLedgerApi.IsData.Class
import PlutusCore

namespace CardanoLedgerApi.V1.Time
open IsData.Class
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)

/-- `POSIXTime` is an alias to `Integer` -/
abbrev POSIXTime := Integer

/-- Whether a bound is inclusive or not -/
abbrev Closure := Bool

/-- IsData instance for Closure -/
instance : IsData Closure := inferInstanceAs (IsData Closure)

/-- type introducing the a positive and a negative infinity bound. -/
inductive InfiniteBound where
  | NegInf : InfiniteBound
  | PosInf : InfiniteBound
deriving Repr

def beqInfiniteBound (x y : InfiniteBound) : Bool :=
  match x, y with
  | .NegInf, .NegInf
  | .PosInf, .PosInf => true
  | _, _ => false

/-- BEq instance for InfiniteBound -/
instance : BEq InfiniteBound := ⟨beqInfiniteBound⟩

/-! DecidableEq instance for InfiniteBound -/
theorem beqInfiniteBound_iff_eq (x y : InfiniteBound) : beqInfiniteBound x y ↔ x = y := by
  cases x <;> cases y <;> simp [beqInfiniteBound]

theorem beqInfiniteBound_false_iff_not_eq (x y : InfiniteBound) :
  beqInfiniteBound x y = false ↔ x ≠ y := by cases x <;> cases y <;> simp [beqInfiniteBound]


def InfiniteBound.decEq (x y : InfiniteBound) : Decidable (Eq x y) :=
  match h:(beqInfiniteBound x y) with
  | true => isTrue ((beqInfiniteBound_iff_eq _ _).1 h)
  | false => isFalse ((beqInfiniteBound_false_iff_not_eq _ _).1 h)

instance : DecidableEq (InfiniteBound) := InfiniteBound.decEq

/-! LawfulBEq instance for InfiniteBound -/
theorem beqInfiniteBound_reflexive (x : InfiniteBound) : beqInfiniteBound x x = true := by
  cases x <;> simp [beqInfiniteBound]

instance : LawfulBEq InfiniteBound where
  eq_of_beq {a b} := (beqInfiniteBound_iff_eq a b).1
  rfl {bs} := by simp [BEq.beq]; apply beqInfiniteBound_reflexive

def ltInfiniteBound (x y : InfiniteBound) : Bool :=
  match x, y with
  | .NegInf, .PosInf => true
  | _, _ => false

/-- LT instance for InfiniteBound -/
instance : LT InfiniteBound where
  lt x y := ltInfiniteBound x y

/-! DecidableLT instance for InfiniteBound -/
theorem ltInfiniteBound_true_imp_lt (x y : InfiniteBound) : ltInfiniteBound x y → x < y := by
  cases x <;> cases y <;> simp [ltInfiniteBound, LT.lt]

theorem ltInfiniteBound_false_imp_not_lt (x y : InfiniteBound) :
  ltInfiniteBound x y = false → ¬ x < y := by
    cases x <;> cases y <;> simp [ltInfiniteBound, LT.lt]

def InfiniteBound.decLt (x y : InfiniteBound) : Decidable (LT.lt x y) :=
  match h:(ltInfiniteBound x y) with
  | true => isTrue (ltInfiniteBound_true_imp_lt _ _ h)
  | false => isFalse (ltInfiniteBound_false_imp_not_lt _ _ h)

instance : DecidableLT InfiniteBound := InfiniteBound.decLt

/-! Std.Irrefl instance for InfiniteBound -/
theorem InfiniteBound.lt_irrefl (x : InfiniteBound) : ¬ x < x := by
    cases x <;> simp [ltInfiniteBound, LT.lt]

instance : Std.Irrefl (. < . : InfiniteBound → InfiniteBound → Prop) where
  irrefl := InfiniteBound.lt_irrefl

/-- LE instance for InfiniteBound -/
instance : LE InfiniteBound where
  le x y := ¬ (y < x)

/-! DecidableLE instance for InfiniteBound -/
instance : DecidableLE InfiniteBound :=
  fun x y => inferInstanceAs (Decidable (¬ (y < x)))

/- Max instance for InfiniteBound -/
instance : Max InfiniteBound where
  max x y := if x < y then y else x

/- Min instance for InfiniteBound -/
instance : Min InfiniteBound where
  min x y := if x < y then x else y


/-- The upper bound of an POSIXTime interval. -/
inductive UpperBound where
  | FiniteUpperBound : POSIXTime → Closure → UpperBound
  | InfiniteUpperBound : InfiniteBound → UpperBound
deriving Repr


def beqUpperBound (x y : UpperBound) : Bool :=
  match x, y with
  | .FiniteUpperBound u1 c1, .FiniteUpperBound u2 c2 => u1 == u2 && c1 == c2
  | .InfiniteUpperBound b1, .InfiniteUpperBound b2 => b1 == b2
  | _, _ => false

/-- BEq instance for UpperBound -/
instance : BEq UpperBound := ⟨beqUpperBound⟩

/-! DecidableEq instance for UpperBound -/
@[simp] theorem beqUpperBound_iff_eq (x y : UpperBound) : beqUpperBound x y ↔ x = y := by
  cases x <;> cases y <;> simp [beqUpperBound]

@[simp] theorem beqUpperBound_false_iff_not_eq (x y : UpperBound) : beqUpperBound x y = false ↔ x ≠ y := by
  cases x <;> cases y <;> simp [beqUpperBound]

def decEqUpperBound (x y : UpperBound) : (Decidable (Eq x y)) :=
 match h:(beqUpperBound x y) with
 | true => isTrue ((beqUpperBound_iff_eq _ _).1 h)
 | false => isFalse ((beqUpperBound_false_iff_not_eq _ _).1 h)

instance : DecidableEq UpperBound := decEqUpperBound

/-! LawfulBEq instance for UpperBound -/
theorem beqUpperBound_reflexive (x : UpperBound) : beqUpperBound x x = true := by
  cases x <;> simp [beqUpperBound]

instance : LawfulBEq UpperBound where
  eq_of_beq {a b} := (beqUpperBound_iff_eq a b).1
  rfl {bs} := by simp [BEq.beq]

def ltUpperBound (x y : UpperBound) : Bool :=
  match x, y with
  | .FiniteUpperBound .., .InfiniteUpperBound .PosInf
  | .InfiniteUpperBound .NegInf, .FiniteUpperBound .. => true
  | .InfiniteUpperBound u1, .InfiniteUpperBound u2 => u1 < u2
  | .FiniteUpperBound u1 c1, .FiniteUpperBound u2 c2 =>
       -- NOTE: x should be strict upperbound upon equality
       u1 < u2 || (u1 == u2 && c1 < c2)
  | .InfiniteUpperBound .PosInf, .FiniteUpperBound ..
  | .FiniteUpperBound .., .InfiniteUpperBound .NegInf => false

/-- LT instance for UpperBound -/
instance : LT UpperBound where
  lt x y := ltUpperBound x y

/-! DecidableLT instance for UpperBound -/
theorem ltUpperBound_true_imp_lt (x y : UpperBound) : ltUpperBound x y → x < y := by
  cases x <;> cases y <;> simp [ltUpperBound, LT.lt]

theorem ltUpperBound_false_imp_not_lt (x y : UpperBound) : ltUpperBound x y = false → ¬ x < y := by
  cases x <;> cases y <;> simp [ltUpperBound, LT.lt]

def decLtUpperBound (x y : UpperBound) : Decidable (LT.lt x y) :=
  match h:(ltUpperBound x y) with
  | true => isTrue (ltUpperBound_true_imp_lt _ _ h)
  | false => isFalse (ltUpperBound_false_imp_not_lt _ _ h)

instance : DecidableLT UpperBound := decLtUpperBound

/-- LE instance for UpperBound -/
instance : LE UpperBound where
  le x y := ¬ (y < x)

/-! DecidableLE instance for UpperBound -/
instance : DecidableLE UpperBound :=
  fun x y => inferInstanceAs (Decidable (¬ (y < x)))

/-! Std.Irrefl instance for UpperBound -/
@[simp] theorem ltUpperBound_same_false (x : UpperBound) : ltUpperBound x x = false := by
  cases x <;> simp [ltUpperBound, Std.Irrefl.irrefl]

theorem UpperBound_lt_irrefl (x : UpperBound) : ¬ x < x := by cases x <;> simp [LT.lt]

instance : Std.Irrefl (. < . : UpperBound → UpperBound → Prop) where
  irrefl := UpperBound_lt_irrefl

/- Max instance for UpperBound -/
instance : Max UpperBound where
  max x y := if x < y then y else x

/- Min instance for UpperBound -/
instance : Min UpperBound where
  min x y := if x < y then x else y

/-- Return the `Data` representation for `InfiniteBound` instance
    NOTE: We don't want to have a specific IsData instance for InfiniteBound,
    as we deliberately seperate finite and infinite bounds at the UpperBound and LowerBound level.
    NOTE: We also impose that encoding an InfiniteBound instance can only be performed from either
    an UpperBound or LowerBound instance.
-/
def infiniteBoundToData (e : InfiniteBound) : Data :=
  match e with
  | .NegInf => mkDataConstr 0
  | .PosInf => mkDataConstr 2

/-- Try to obtain an `InfiniteBound` instance from `Data` instance.
    NOTE: We don't want to have a specific IsData instance for InfiniteBound,
    as we deliberately seperate finite and infinite bounds at the UpperBound and LowerBound level.
    NOTE: We also impose that decoding an InfiniteBound instance can only be performed from either
    an UpperBound or LowerBound instance.
-/
def infiniteBoundFromData (dat : Data) : Option InfiniteBound :=
  match dat with
  | Data.Constr 0 [] => some .NegInf
  | Data.Constr 2 [] => some .PosInf
  | _ => none

/-- IsData instance for UpperBound -/
instance : IsData UpperBound where
  toData
  | .InfiniteUpperBound u =>
       -- true closure by default for infinite bound
       mkDataConstr 0 [infiniteBoundToData u, IsData.toData true]
  | .FiniteUpperBound u c =>
       mkDataConstr 0 [mkDataConstr 1 [IsData.toData u], IsData.toData c]
  fromData
  | Data.Constr 0 [r_e, r_c] =>
     match IsData.fromData r_c with
     | some c =>
        if let some b := infiniteBoundFromData r_e
        then some (.InfiniteUpperBound b)
        else match r_e with
             | Data.Constr 1 [r_f] =>
                if let some b := IsData.fromData r_f
                then some (.FiniteUpperBound b c)
                else none
             | _ => none
     | none => none
  | _ => none


/-- The lower bound of a POSIXTime interval. -/
inductive LowerBound where
  | FiniteLowerBound : POSIXTime → Closure → LowerBound
  | InfiniteLowerBound : InfiniteBound → LowerBound
deriving Repr


def beqLowerBound (x y : LowerBound) : Bool :=
  match x, y with
  | .FiniteLowerBound l1 c1, .FiniteLowerBound l2 c2 => l1 == l2 && c1 == c2
  | .InfiniteLowerBound b1, .InfiniteLowerBound b2 => b1 == b2
  | _, _ => false

/-- BEq instance for LowerBound -/
instance : BEq LowerBound := ⟨beqLowerBound⟩

/-! DecidableEq instance for LowerBound -/
@[simp] theorem beqLowerBound_iff_eq (x y : LowerBound) : beqLowerBound x y ↔ x = y := by
  cases x <;> cases y <;> simp [beqLowerBound]

@[simp] theorem beqLowerBound_false_iff_not_eq (x y : LowerBound) : beqLowerBound x y = false ↔ x ≠ y := by
  cases x <;> cases y <;> simp [beqLowerBound]

def decEqLowerBound (x y : LowerBound) : (Decidable (Eq x y)) :=
 match h:(beqLowerBound x y) with
 | true => isTrue ((beqLowerBound_iff_eq _ _).1 h)
 | false => isFalse ((beqLowerBound_false_iff_not_eq _ _).1 h)

instance : DecidableEq LowerBound := decEqLowerBound

/-! LawfulBEq instance for LowerBound -/
theorem beqLowerBound_reflexive (x : LowerBound) : beqLowerBound x x = true := by
  cases x <;> simp [beqLowerBound]

instance : LawfulBEq LowerBound where
  eq_of_beq {a b} := (beqLowerBound_iff_eq a b).1
  rfl {bs} := by simp [BEq.beq]

def ltLowerBound (x y : LowerBound) : Bool :=
  match x, y with
  | .FiniteLowerBound .., .InfiniteLowerBound .PosInf
  | .InfiniteLowerBound .NegInf, .FiniteLowerBound .. => true
  | .InfiniteLowerBound u1, .InfiniteLowerBound u2 => u1 < u2
  | .FiniteLowerBound u1 c1, .FiniteLowerBound u2 c2 =>
       -- NOTE: y should be strict lowerbound upon equality
       u1 < u2 || (u1 == u2 && c2 < c1)
  | .InfiniteLowerBound .PosInf, .FiniteLowerBound ..
  | .FiniteLowerBound .., .InfiniteLowerBound .NegInf => false

/-- LT instance for LowerBound -/
instance : LT LowerBound where
  lt x y := ltLowerBound x y

/-! DecidableLT instance for LowerBound -/
theorem ltLowerBound_true_imp_lt (x y : LowerBound) : ltLowerBound x y → x < y := by
  cases x <;> cases y <;> simp [ltLowerBound, LT.lt]

theorem ltLowerBound_false_imp_not_lt (x y : LowerBound) : ltLowerBound x y = false → ¬ x < y := by
    cases x <;> cases y <;> simp [ltLowerBound, LT.lt]

def decLtLowerBound (x y : LowerBound) : Decidable (LT.lt x y) :=
  match h:(ltLowerBound x y) with
  | true => isTrue (ltLowerBound_true_imp_lt _ _ h)
  | false => isFalse (ltLowerBound_false_imp_not_lt _ _ h)

instance : DecidableLT LowerBound := decLtLowerBound

/-! Std.Irrefl instance for LowerBound -/
@[simp] theorem ltLowerBound_same_false (x : LowerBound) : ltLowerBound x x = false := by
  cases x <;> simp [ltLowerBound, Std.Irrefl.irrefl]

theorem LowerBound_lt_irrefl (x : LowerBound) : ¬ x < x := by cases x <;> simp [LT.lt]

instance : Std.Irrefl (. < . : LowerBound → LowerBound → Prop) where
  irrefl := LowerBound_lt_irrefl

/-- LE instance for LowerBound -/
instance : LE LowerBound where
  le x y := ¬ (y < x)

/-! DecidableLE instance for LowerBound -/
instance : DecidableLE LowerBound :=
  fun x y => inferInstanceAs (Decidable (¬ (y < x)))

/- Max instance for LowerBound -/
instance : Max LowerBound where
  max x y := if x < y then y else x

/- Min instance for LowerBound -/
instance : Min LowerBound where
  min x y := if x < y then x else y


/-- IsData instance for LowerBound -/
instance : IsData LowerBound where
  toData
  | .InfiniteLowerBound u =>
       -- true closure by default for infinite bound
       mkDataConstr 0 [infiniteBoundToData u, IsData.toData true]
  | .FiniteLowerBound u c =>
       mkDataConstr 0 [mkDataConstr 1 [IsData.toData u], IsData.toData c]
  fromData
  | Data.Constr 0 [r_e, r_c] =>
     match IsData.fromData r_c with
     | some c =>
        if let some b := infiniteBoundFromData r_e
        then some (.InfiniteLowerBound b)
        else match r_e with
             | Data.Constr 1 [r_f] =>
                if let some b := IsData.fromData r_f
                then some (.FiniteLowerBound b c)
                else none
             | _ => none
     | none => none
  | _ => none

/-- A POSIXTime interval that may be either closed or open at either end. -/
structure POSIXTimeRange where
  ivFrom : LowerBound
  ivTo : UpperBound
deriving Repr

def beqPOSIXTimeRange (x y : POSIXTimeRange) : Bool :=
    x.ivFrom == y.ivFrom && x.ivTo == y.ivTo

/-- BEq instance for POSIXTimeRange -/
instance : BEq POSIXTimeRange := ⟨beqPOSIXTimeRange⟩

/-! DecidableEq instance for POSIXTimeRange -/
@[simp] theorem beqPOSIXTimeRange_iff_eq (x y : POSIXTimeRange) : beqPOSIXTimeRange x y ↔ x = y := by
  match x, y with
  | POSIXTimeRange.mk .., POSIXTimeRange.mk .. => simp [beqPOSIXTimeRange]

@[simp] theorem beqPOSIXTimeRange_false_iff_not_eq (x y : POSIXTimeRange) :
  beqPOSIXTimeRange x y = false ↔ x ≠ y := by
    match x, y with
    | POSIXTimeRange.mk .., POSIXTimeRange.mk .. => simp [beqPOSIXTimeRange]

def POSIXTimeRange.decEq (x y : POSIXTimeRange) : Decidable (Eq x y) :=
  match h:(beqPOSIXTimeRange x y) with
  | true => isTrue ((beqPOSIXTimeRange_iff_eq _ _).1 h)
  | false => isFalse ((beqPOSIXTimeRange_false_iff_not_eq _ _).1 h)

instance : DecidableEq POSIXTimeRange := POSIXTimeRange.decEq

/-! LawfulBEq instance for POSIXTimeRange -/
theorem beqPOSIXTimeRange_reflexive (x : POSIXTimeRange) : beqPOSIXTimeRange x x = true := by
  simp [beqPOSIXTimeRange]

instance : LawfulBEq POSIXTimeRange where
  eq_of_beq {a b} := (beqPOSIXTimeRange_iff_eq a b).1
  rfl {bs} := by simp [BEq.beq]


/-- IsData instance for POSIXTimeRange -/
instance : IsData POSIXTimeRange where
  toData x := mkDataConstr 0 [IsData.toData x.ivFrom, IsData.toData x.ivTo]
  fromData
  | Data.Constr 0 [r_from, r_to] =>
      match IsData.fromData r_from, IsData.fromData r_to with
      | some ivFrom, some ivTo => some ⟨ivFrom, ivTo⟩
      | _, _ => none
  | _ => none



/-! Constants -/

/-- Create an `POSIXTimeRange` that contains every possible values, i.e., [-∞,+∞]. -/
def everything : POSIXTimeRange := ⟨.InfiniteLowerBound .NegInf, .InfiniteUpperBound .PosInf⟩

/-- Create an `POSIXTimeRange` that contains no value, i.e., arbitrarily set to [+∞,-∞]. -/
def empty : POSIXTimeRange := ⟨.InfiniteLowerBound .PosInf, .InfiniteUpperBound .NegInf⟩


/-! Constructors -/

/-- Create a strict upper bound from a `POSIXTime`.
    The resulting bound includes all values that are (strictly) smaller than the input value.
-/
def strictUpperBound (x : POSIXTime) : UpperBound :=
  .FiniteUpperBound x false

/-- Create a strict lower bound from a `POSIXTime`.
    The resulting bound includes all values that are (strictly) greater than the input value.
-/
def strictLowerBound (x : POSIXTime) : LowerBound :=
  .FiniteLowerBound x false

/-- Create a lower bound from a `POSIXTime`.
    The resulting bound includes all values that are equal or greater than the input value.
-/
def lowerBound (x : POSIXTime) : LowerBound :=
  .FiniteLowerBound x true

/-- Create an upper bound from a `POSIXTime`
    The resulting bound includes all values that are equal or smaller than the input value.
-/
def upperBound (x : POSIXTime) : UpperBound :=
  .FiniteUpperBound x true

/-- Create an `POSIXTimeRange` that includes all values greater than or equal to `a`, i.e., [a,+∞]. -/
def after (a : POSIXTime) : POSIXTimeRange := ⟨lowerBound a, .InfiniteUpperBound .PosInf⟩

/-- Create an `POSIXTimeRange` that includes all values greater than `a`, i.e., (a,+∞]. -/
def entirelyAfter (a : POSIXTime) : POSIXTimeRange := ⟨strictLowerBound a, .InfiniteUpperBound .PosInf⟩

/-- Create an `POSIXTimeRange` that includes all values that are less than or equal to `a`, i.e., [-∞, a]. -/
def before (a : POSIXTime) : POSIXTimeRange := ⟨.InfiniteLowerBound .NegInf, upperBound a⟩

/-- Create an `POSIXTimeRange` that includes all values that are less than `a`, i.e., [-∞, a). -/
def entirelyBefore (a : POSIXTime) : POSIXTimeRange := ⟨.InfiniteLowerBound .NegInf, strictUpperBound a⟩

/-- Create an `POSIXTimeRange` that includes all values that between `a` and `b`, i.e., [a, b]. -/
def between (a b : POSIXTime) : POSIXTimeRange := ⟨lowerBound a, upperBound b⟩

/-- Create an `POSIXTimeRange` that includes all values that between `a` and `b`, excluding the bounds , i.e., (a, b). -/
def entirelyBetween (a b : POSIXTime) : POSIXTimeRange := ⟨strictLowerBound a, strictUpperBound b⟩


/-! Operators -/

/-- Compute the smallest interval containing `a` and `b`. -/
def hull (a : POSIXTimeRange) (b : POSIXTimeRange) : POSIXTimeRange :=
  ⟨min a.ivFrom b.ivFrom, max a.ivTo b.ivTo⟩

/-- Compute the largest interval containing `a` and `b`. -/
def intersection (a : POSIXTimeRange) (b : POSIXTimeRange) : POSIXTimeRange :=
  ⟨max a.ivFrom b.ivFrom, min a.ivTo b.ivTo⟩


/-! Predicates -/

/-- Determine whether a `POSIXTimeRange` is empty, i.e., the interval contains no value -/
def isEmpty (range : POSIXTimeRange) : Bool :=
  match range.ivFrom, range.ivTo with
  | .InfiniteLowerBound l1, .InfiniteUpperBound u1 => u1 < l1
  | .FiniteLowerBound l1 c1, .FiniteUpperBound u1 c2 =>
       (u1 < l1) || ((l1 == u1 || l1 == u1 - 1) && (!c1 || !c2))
  | .FiniteLowerBound .., .InfiniteUpperBound .NegInf
  | .InfiniteLowerBound .PosInf, .FiniteUpperBound .. => true
  | .FiniteLowerBound .., .InfiniteUpperBound .PosInf
  | .InfiniteLowerBound .NegInf, .FiniteUpperBound .. => false


/-- Check whether the second `POSIXTimeRange` is fully included in the first one -/
def includes (a b : POSIXTimeRange) : Bool :=
  a.ivFrom ≤ b.ivFrom && b.ivTo ≤ a.ivTo

/-- Check whether a `POSIXTime` is contained within the `POSIXTimeRange`. -/
def contains (p : POSIXTime) (range : POSIXTimeRange) : Bool :=
   includes range (between p p)

/-- Check whether the `POSIXTimeRange` is entirely after the given `POSIXTime`. -/
def isEntirelyAfter (a : POSIXTime) (range : POSIXTimeRange) : Bool :=
  lowerBound a < range.ivFrom

/-- Check whether the `POSIXTimeRange` is entirely before the given `POSIXTime`. -/
def isEntirelyBefore (a : POSIXTime) (range : POSIXTimeRange) : Bool :=
  upperBound a > range.ivTo


end CardanoLedgerApi.V1.Time
