import Tests.Equivalence.Support

namespace Tests.Equivalence.Mapping
open Support Lean
open _root_.Equivalence.Mapping
open PlutusCore.Data (Data)

def spec : Spec := {
  source := [⟨"amount", 1⟩, ⟨"rate", 100⟩]
  target := [.quantity ⟨"rate", 10000⟩, .quantity ⟨"amount", 1⟩, .extraData, .fixed 0]
  oldOutput := .integer
  newOutput := .dataInteger }

def plan : Plan := ⟨2, 1, [.source 1 100, .source 0 1, .extra 0, .fixed 0]⟩
example : infer spec = .ok plan := rfl

-- Coverage: every old input is retained, for every metadata value.
theorem roundtrip (amount percent : Int) (metadata : Data) :
    (plan.encode [amount, percent] [metadata]).bind plan.recover =
      some [amount, percent] := by
  simp [plan, Plan.encode, Plan.recover, integer, List.range_succ, List.mapM, List.mapM.loop, List.find?]

example : infer { spec with target := [.quantity ⟨"rate", 10000⟩] } =
    .error "A source quantity is missing from the target" := rfl
example : infer { spec with source := [⟨"rate", 100⟩, ⟨"rate", 100⟩] } =
    .error "Ambiguous source quantity names" := rfl
example : infer { spec with source := [⟨"amount", 0⟩, ⟨"rate", 100⟩] } =
    .error "Source units must be positive" := rfl
example : infer { spec with target := [.quantity ⟨"rate", 1⟩] } =
    .error "No exact integer unit expansion for rate" := rfl
example : infer { spec with target := [.quantity ⟨"price", 100⟩] } =
    .error "No source quantity named price" := rfl
example : plan.encode [1] [.I 0] = none := rfl
example : plan.encode [1, 2] [] = none := rfl
example : plan.recover [integer 2550, integer 1000, .Const (.Data (.I 0)), integer 0] = none := by decide

def old : String :=
  "(lam amount (lam percent [[(builtin divideInteger) [[(builtin multiplyInteger) amount] percent]] (con integer 100)]))"

def new : String :=
  "(lam rate (lam amount (lam metadata (lam bonus [(builtin iData) [[(builtin addInteger) " ++
  "[[(builtin divideInteger) [[(builtin multiplyInteger) amount] rate]] (con integer 10000)]] bonus]]))))"

def settings : Support.Config := {
  mode := "function", inputs := "integer", mapping := some spec
  steps := 200, timeout := 20, wallTimeout := 60 }

#eval show IO Unit from do
  let report ← comparePrograms old new settings
  verdict report "equivalent"
  noCounterexample report
  expect report ["mapping_plan", "sourceCount"] (2 : Nat)
  expect report ["mapping_plan", "extraCount"] (1 : Nat)
  -- Wrong units must produce an actual replayed difference, not a solver claim alone.
  let wrongScale := { spec with target :=
    [.quantity ⟨"rate", 100⟩, .quantity ⟨"amount", 1⟩, .extraData, .fixed 0] }
  let report ← comparePrograms old new { settings with mapping := some wrongScale }
  verdict report "inequivalent"
  let w ← witness report
  expect w ["direction"] "mapped_function_outcomes"
  discard (field w ["old_arguments"])
  discard (field w ["new_arguments"])
  let bonus := { spec with target :=
    [.quantity ⟨"rate", 10000⟩, .quantity ⟨"amount", 1⟩, .extraData, .fixed 5] }
  verdict (← comparePrograms old new { settings with mapping := some bonus }) "inequivalent"

-- Identical program text is insufficient when arguments or observations differ.
#eval show IO Unit from do
  let scaling : Spec := { source := [⟨"x", 1⟩], target := [.quantity ⟨"x", 2⟩] }
  let report ← comparePrograms "(lam x x)" "(lam x x)" { settings with mapping := some scaling }
  verdict report "inequivalent"
  discard (witness report)
  check report (report.getObjVal? "derived_queries").toOption.isNone "Mapping bypassed by program identity"
  let badOutput := { scaling with target := [.quantity ⟨"x", 1⟩], oldOutput := .dataInteger, newOutput := .dataInteger }
  verdict (← comparePrograms "(lam x x)" "(lam x x)" { settings with mapping := some badOutput }) "inconclusive"

-- Extras are universally quantified, including values that the program inspects.
#eval show IO Unit from do
  let extra : Spec := { source := [⟨"x", 1⟩], target := [.quantity ⟨"x", 1⟩, .extraData] }
  let report ← comparePrograms "(lam x (con integer 0))"
    "(lam x (lam metadata [(builtin unIData) metadata]))" { settings with mapping := some extra }
  verdict report "inequivalent"
  discard (witness report)
  verdict (← comparePrograms old new { settings with steps := 1 }) "inconclusive"

-- Library callers also get schema and scope validation, independently of the CLI.
#eval show IO Unit from do
  for c in [{ settings.toConfig with mode := "validator" },
      { settings.toConfig with bounded := true },
      { settings.toConfig with inputs := "data" },
      { settings.toConfig with mapping := some { spec with target := [] } }] do
    unless c.validate matches .error _ do throw <| IO.userError "Invalid mapping configuration accepted"

#print axioms roundtrip
end Tests.Equivalence.Mapping
