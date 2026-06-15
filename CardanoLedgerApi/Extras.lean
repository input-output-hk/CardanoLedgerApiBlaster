
namespace CardanoLedgerApi.Extras

def ltOption [LT α] [DecidableLT α] (x y : Option α) : Bool :=
  match x, y with
  | .none, .some _ => true
  | .some a, .some b => a < b
  | _, _ => false

/-! DecidableLT instance for Option -/
theorem ltOption_true_imp_lt [LT α] [DecidableLT α] (x y : Option α) : ltOption x y → x < y := by
  cases x <;> cases y <;> simp [ltOption, LT.lt, Option.lt]

theorem ltOption_false_imp_not_lt [LT α] [DecidableLT α] (x y : Option α) : ltOption x y = false → ¬ x < y := by
  cases x <;> cases y <;> simp [ltOption, LT.lt, Option.lt]

def decLtOption [LT α] [DecidableLT α] (x y : Option α) : Decidable (LT.lt x y) :=
  match h:(ltOption x y) with
  | true => isTrue (ltOption_true_imp_lt _ _ h)
  | false => isFalse (ltOption_false_imp_not_lt _ _ h)

instance [LT α] [DecidableLT α] : DecidableLT (Option α) := decLtOption

/-- LE instance for Option -/
instance [LT α] : LE (Option α) where
  le x y := ¬ (y < x)

def leqOption [LT α] [DecidableLT α] (x y : Option α) : Bool := !(y < x)

/-! DecidableLE instance for Option -/
theorem leqOption_true_imp_le [LT α] [DecidableLT α] (x y : Option α) : leqOption x y → x ≤ y := by
  cases x <;> cases y <;> simp [leqOption, LE.le]

theorem leqOption_false_imp_not_le [LT α] [DecidableLT α] (x y : Option α) : leqOption x y = false → ¬ x ≤ y := by
  cases x <;> cases y <;> simp [leqOption, LE.le]

def decLeqOption [LT α] [DecidableLT α] (x y : Option α) : Decidable (LE.le x y) :=
  match h:(leqOption x y) with
  | true => isTrue (leqOption_true_imp_le _ _ h)
  | false => isFalse (leqOption_false_imp_not_le _ _ h)

instance [LT α] [DecidableLT α] : DecidableLE (Option α) := decLeqOption

/-! Std.Irrefl instance for Option -/
@[simp] theorem ltOptionD_same_false [LT α] [DecidableLT α] [Std.Irrefl (. < . : α → α → Prop)] (x : Option α) :
  ltOption x x = false := by cases x <;> simp [ltOption, Std.Irrefl.irrefl]

theorem Option_lt_irrefl [LT α] [DecidableLT α] [Std.Irrefl (. < . : α → α → Prop)] (x : Option α) : ¬ x < x :=
  by cases x <;> simp [Std.Irrefl.irrefl]

instance [LT α] [DecidableLT α] [Std.Irrefl (. < . : α → α → Prop)] : Std.Irrefl (. < . : (Option α) → (Option α) → Prop) where
  irrefl := Option_lt_irrefl


end CardanoLedgerApi.Extras
