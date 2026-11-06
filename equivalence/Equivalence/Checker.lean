import Equivalence.Queries
import PlutusCore.Smt.Model
import Equivalence.ValidContextModel
import Equivalence.Solver

/-!
Provides the library entry point for checking two decoded UPLC programs.
Plans symbolic queries, gathers solver evidence and replays concrete witnesses.
Classifies function and validator results, including vacuous and inconclusive checks.
-/

open Lean System

namespace Equivalence.Checker

/-- Use the toolchain the checker was built with, including outside the repo.
    This is evaluated at compile time, so checking invokes neither Lean nor Lake. -/
elab "toolchain_root%" : term => do
  return toExpr (← findSysroot).toString

def toolchainRoot : String := toolchain_root%

/-- Include path dependencies as well as Lake's git-package cache. -/
elab "module_search_path%" : term => do
  return toExpr ((← searchPathRef.get).map FilePath.toString)

def moduleSearchPath : List String := module_search_path%

/-- Semantic options for checking decoded programs, independent of any CLI. -/
structure Config extends ValidContext.Limits where
  mode : String := "validator"
  bounded : Bool := false
  steps : Nat := 100000
  language : String := "PlutusV3"
  inputs : String := "valid-context"
  equivalence : Bool := false
  budget : Option (Nat × Nat) := none
  timeout : Nat := 20
  skipOldRejected : Bool := false

/-- Steps restrict execution in bounded mode; otherwise they only guard analysis. -/
def Config.stepLimitFields (c : Config) : List (String × Json) := [
  ("steps", toJson c.steps), ("bounded", toJson c.bounded),
  ("step_limit_kind", toJson (if c.bounded then "execution_bound" else "analysis_guard"))]

/-- Check semantic option combinations for library callers as well as the CLI. -/
def Config.validate (c : Config) : Except String Unit := do
  unless ["validator", "function"].contains c.mode do throw s!"unsupported mode: {c.mode}"
  if c.steps == 0 then throw "step limit must be positive"
  if c.timeout == 0 then throw "solver timeout must be positive"
  if c.mode == "validator" && !c.bounded && c.budget.isNone then
    throw "validator checking requires --budget CPU MEMORY or --bounded --steps N"
  if c.mode == "function" then
    unless ["integer", "data", "data3"].contains c.inputs do
      throw "function mode supports --inputs integer, data or data3"
    if c.equivalence && !c.bounded then
      throw "function --equivalence requires --bounded; strict function mode already compares both outcomes"
    if c.skipOldRejected then
      throw "--skip-old-rejected is a validator option"
  if c.mode == "validator" then
    if c.inputs != "valid-context" then
      throw s!"unsupported validator input mode: {c.inputs}; use valid-context"
    if c.language != "PlutusV3" then throw "valid-context requires --language PlutusV3"
  unless ["PlutusV1", "PlutusV2", "PlutusV3"].contains c.language do
    throw s!"unsupported language: {c.language}"

def checksLedger (c : Config) : Bool := c.mode == "validator"

def validLedgerContext (c : Config) (raw : PlutusCore.Data.Data) : Bool :=
  Ledger.validContext raw && ValidContext.contains c.toLimits raw

def auditLedgerContext (_c : Config) (raw : PlutusCore.Data.Data) : Json :=
  Ledger.audit raw

/-- One query description drives solving, reports and emitted Lean source.
    Side indices select the old/left (0) or new/right (1) program. -/
structure Query where
  name : String
  declaration : Name
  sides : Array Nat

def functionQueryName (c : Config) : String :=
  if c.bounded then
    if c.equivalence then "bounded_function_equivalent" else "bounded_function_preserved"
  else "function_equivalent"

def Query.wantsCounterexample (query : Query) : Bool :=
  query.name == "function_equivalent" || query.name == "bounded_function_equivalent" ||
  query.name == "bounded_function_preserved" || query.name.endsWith "no_acceptance_regression" ||
  query.name == "old_rejected" || query.name.endsWith "acceptance_preserved"

def Query.description (query : Query) : String :=
  match query.name with
  | "function_equivalent" => "comparing function outcomes and returned values"
  | "bounded_function_preserved" => "preserving OLD constant results within the supplied limits"
  | "bounded_function_equivalent" => "comparing bounded function observations (constant or none)"
  | "old_rejected" => "checking whether OLD rejects every input"
  | "new_rejected" => "checking whether NEW rejects every input"
  | "no_acceptance_regression" => "checking for an OLD-to-NEW acceptance regression"
  | "acceptance_preserved" => "proving OLD-to-NEW acceptance preservation"
  | "reverse_no_acceptance_regression" => "checking for a NEW-to-OLD acceptance regression"
  | "reverse_acceptance_preserved" => "proving NEW-to-OLD acceptance preservation"
  | _ => query.name

/-- Domains choose declarations; the check determines query names and sides. -/
def queries (c : Config) : Array Query :=
  if c.mode == "function" then
    let declaration := if c.bounded && !c.equivalence then
        if c.inputs == "data" then ``Queries.dataBoundedFunctionPreserved
        else if c.inputs == "data3" then ``Queries.data3BoundedFunctionPreserved
        else ``Queries.integerBoundedFunctionPreserved
      else if c.bounded then
        if c.inputs == "data" then ``Queries.dataBoundedFunctionEquivalent
        else if c.inputs == "data3" then ``Queries.data3BoundedFunctionEquivalent
        else ``Queries.integerBoundedFunctionEquivalent
      else if c.inputs == "data" then ``Queries.dataFunctionEquivalent
      else if c.inputs == "data3" then ``Queries.data3FunctionEquivalent
      else ``Queries.integerFunctionEquivalent
    #[⟨functionQueryName c, declaration, #[0, 1]⟩]
  else
    let (noRegression, preserved) := (``Queries.noAcceptanceRegression, ``Queries.acceptancePreserved)
    let forward : Array Query := #[
      ⟨"acceptance_preserved", preserved, #[0, 1]⟩,
      ⟨"no_acceptance_regression", noRegression, #[0, 1]⟩]
    let rejectedDeclaration := ``Queries.rejected
    let rejected := fun (name : String) (side : Nat) =>
      #[Query.mk name rejectedDeclaration #[side]]
    let comparisons := if c.equivalence then #[
      ⟨"acceptance_preserved", preserved, #[0, 1]⟩,
      ⟨"reverse_acceptance_preserved", preserved, #[1, 0]⟩,
      ⟨"no_acceptance_regression", noRegression, #[0, 1]⟩,
      ⟨"reverse_no_acceptance_regression", noRegression, #[1, 0]⟩]
      else forward
    comparisons ++ (if c.skipOldRejected then #[] else rejected "old_rejected" 0) ++
      (if c.equivalence then rejected "new_rejected" 1 else #[])

def queryNames (c : Config) : Array String := (queries c).map Query.name

/-- Rejection settles only the direction starting at that script. -/
def rejectionEvidence (c : Config) (query : Query) (results : Array Blaster.Smt.Result) : Option String :=
  let name := if query.sides[0]? == some 0 then "old_rejected" else "new_rejected"
  if query.name == name then none
  else match results[(queryNames c).idxOf name]? with
    | some .Valid => some name
    | _ => none

/-- Rejection settles its own direction; preservation also implies no regression.
    These implications are checked by the Acceptance lemmas. -/
def queryEvidence (c : Config) (query : Query) (results : Array Blaster.Smt.Result) : Option String :=
  (rejectionEvidence c query results).orElse fun _ => do
    guard (query.name.endsWith "no_acceptance_regression")
    let preserved := if query.sides[0]? == some 0 then "acceptance_preserved" else "reverse_acceptance_preserved"
    guard (results[(queryNames c).idxOf preserved]? matches some .Valid)
    return preserved

def inputDomain (c : Config) : String :=
  if c.mode == "validator" then
    s!"Structured V3 spending contexts with 0..{c.maxInputs} independently symbolic inputs, 0..{c.maxOutputs} outputs and 0..{c.maxSigners} signer byte strings; present script datum; typed independent input and spending references; input pubkey/script credentials without staking and absent/hash/inline datums; outputs have arbitrary addresses and inline datums; no reference scripts; each value has an ADA entry and one independent policy/token entry; arbitrary Data validity range, datum, redeemer and unused fields; unbounded integers and byte strings; symbolic queries require CardanoLedgerApi.V3.validSpendingContext; concrete witnesses and counterexamples are independently ledger-validated and natively replayed; model validity does not establish on-chain reachability"
  else if c.inputs == "integer" then "all integers, encoded as raw UPLC integer constants"
  else if c.inputs == "data" then "all Plutus Data values as a single function argument"
  else "all triples of Plutus Data as function arguments"

def status : Blaster.Smt.Result → String
  | .Valid => "valid"
  | .Falsified _ => "falsified"
  | .Undetermined => "undetermined"

/-- A concrete valid member witnesses nonemptiness, not acceptance by OLD. -/
def nativeDomainWitness (c : Config) : Option PlutusCore.Data.Data :=
  if checksLedger c then do
    let raw ← ValidContext.validContext c.toLimits
    if validLedgerContext c raw then some raw else none
  else none

/-- Construct the per-argument property independently of context enumeration. -/
def queryPredicate (c : Config) (query : Query) (programs : Array Expr) : MetaM Expr := do
  let (cpu, memory) := c.budget.getD (0, 0)
  let limits := #[mkRawNatLit cpu, mkRawNatLit memory, toExpr (c.language == "PlutusV3")]
  if c.mode == "function" then
    return mkAppN (mkConst query.declaration) (query.sides.map (programs[·]!) ++
      limits ++ #[toExpr c.budget.isSome, mkRawNatLit c.steps])
  Meta.withLocalDeclD `args (mkApp (mkConst ``List [.zero])
      (mkConst ``PlutusCore.UPLC.Term.Term)) fun args => do
    let body := mkAppN (mkConst query.declaration) (#[args] ++ query.sides.map (programs[·]!) ++
      limits ++ #[toExpr c.bounded, toExpr c.budget.isSome, mkRawNatLit c.steps])
    let valid := mkApp (mkConst ``Ledger.validArguments) args
    let premise ← Meta.mkEq valid (toExpr true)
    -- Establish ledger validity before specializing either script. In particular,
    -- invalid zero-input frames must not expand the symbolic CEK execution.
    let guarded ← mkArrow premise body
    Meta.mkLambdaFVars #[args] guarded

def queryProposition (c : Config) (query : Query) (programs : Array Expr) : MetaM Expr := do
  let predicate ← queryPredicate c query programs
  if c.mode == "function" then return predicate
  ValidContext.proposition c.toLimits predicate

def report (verdict explanation : String) (fields : List (String × Json) := []) : Json :=
  Json.mkObj ([("verdict", toJson verdict), ("explanation", toJson explanation)] ++ fields)

/-- Blaster returns model values as strings, e.g. `n: (- 42)\n`.
    Callers with multiple integer parameters also match their binder names. -/
def modelInteger (binding : String) : Option Int :=
  (Blaster.Smt.Model.integerBinding binding).map Prod.snd

def valueJson : PlutusCore.UPLC.CekValue.CekValue → Json
  | .VCon (.Integer n) => Json.mkObj [("kind", toJson "integer"), ("value", toJson n)]
  | .VCon .Unit => Json.mkObj [("kind", toJson "unit")]
  | value => Json.mkObj [("kind", toJson "other"), ("value", toJson (reprStr value))]

def budgetOutcomeJson (v3 : Bool) (result : Acceptance.Result) (bounded := false) (budgeted := true) : Json :=
  let fields := match result with
    | .success value spent => [("result", valueJson value)] ++
        (if budgeted then [("spent_cpu", toJson spent.exBudgetCPU.unExCPU),
          ("spent_memory", toJson spent.exBudgetMemory.unExMemory)] else [])
    | .error => [("kind", toJson "error")]
    | .budgetExhausted => [("kind", toJson "budget_exhausted")]
    | .unfinished => [("kind", toJson "unfinished")]
  Json.mkObj (("accepts", toJson (Acceptance.accepts v3 (Function.observeValidator bounded result))) :: fields)

def functionOutcomeJson (budgeted : Bool) (result : Acceptance.Result) : Json :=
  match result with
  | .success value spent => Json.mkObj ([("kind", toJson "success"), ("result", valueJson value)] ++
      (if budgeted then [("spent_cpu", toJson spent.exBudgetCPU.unExCPU),
        ("spent_memory", toJson spent.exBudgetMemory.unExMemory)] else []))
  | .error => Json.mkObj [("kind", toJson "error")]
  | .budgetExhausted => Json.mkObj [("kind", toJson "budget_exhausted")]
  | .unfinished => Json.mkObj [("kind", toJson "unfinished")]

def replayWitness (c : Config) (left right : PlutusCore.UPLC.Term.Program)
    (model : List String) (reverse := false) (acceptanceOnly := false) : Json := Id.run do
  let (cpu, memory) := c.budget.getD (0, 0)
  let v3 := c.language == "PlutusV3"
  let replay := fun args input => do
    let execute := fun program => Function.execute program args cpu memory v3 c.budget.isSome c.steps
    let old := execute left
    let new := execute right
    let oldObserved := Function.observeValidator c.bounded old
    let newObserved := Function.observeValidator c.bounded new
    let reproduces := if c.mode == "function" then
        if c.bounded then
          if c.equivalence then !Function.boundedSame old new else !Function.boundedPreserved old new
        else Function.same old new == some false
      else if acceptanceOnly then Acceptance.accepts v3 oldObserved == some true
      else if reverse then Acceptance.regression v3 newObserved oldObserved
      else Acceptance.regression v3 oldObserved newObserved
    if reproduces then
      let outcome := if c.mode == "function" then functionOutcomeJson c.budget.isSome
        else fun result => budgetOutcomeJson v3 result c.bounded c.budget.isSome
      let validity := if c.mode == "function" then [] else match args with
        | [.Const (.Data context)] => [("ledger_validity", auditLedgerContext c context)]
        | _ => []
      some (Json.mkObj ([("input", input), ("old", outcome old),
        ("new", outcome new),
        ("direction", toJson (if c.mode == "function" then "function_outcomes" else if acceptanceOnly then "old_acceptance" else if reverse then "new_to_old" else "old_to_new")),
        ("replayed", toJson true)] ++ validity))
    else none
  let replayContext := fun args => do
    let [.Const (.Data context)] := args | none
    if checksLedger c && !validLedgerContext c context then none
    else replay args (PlutusCore.Data.toDetailedJson context)
  -- Optimization can reduce a universally false query to False without asking
  -- Z3 for a model. Try zero inputs too, but still require a successful replay.
  if checksLedger c then
    for context in ValidContext.modelContexts c.toLimits model ++ ValidContext.modelContexts c.toLimits [] do
      if let some witness := replayContext (Queries.contextArgs context) then return witness
  else if c.inputs == "data" then
    let candidates := (model.filterMap PlutusCore.Smt.Model.dataBinding).map Prod.snd ++ [.I 0]
    for context in candidates do
      if let some witness := replayContext (Queries.contextArgs context) then
        return witness
  else if c.inputs == "data3" then
    let bindings := model.filterMap PlutusCore.Smt.Model.dataBinding
    let find := fun name => bindings.lookup name
    let zero := PlutusCore.Data.Data.I 0
    let candidates := [((find "datum").getD zero, (find "redeemer").getD zero, (find "context").getD zero),
      (zero, zero, zero)]
    for (datum, redeemer, context) in candidates do
      let input := Json.mkObj [("datum", PlutusCore.Data.toDetailedJson datum),
        ("redeemer", PlutusCore.Data.toDetailedJson redeemer), ("context", PlutusCore.Data.toDetailedJson context)]
      if let some witness := replay (Queries.dataArgs datum redeemer context) input then
        return witness
  else
    let candidates := model.filterMap modelInteger ++ [0]
    for n in candidates do
      if let some witness := replay (Queries.args n) (toJson n) then
        return witness
  let kind := if c.inputs == "integer" then "an integer" else "a Data"
  return Json.mkObj [("replayed", toJson false), ("model", toJson (model.map String.trim)),
    ("reason", toJson s!"Could not extract and replay {kind} witness from Blaster's model.")]

def replayCounterexample (c : Config) (left right : PlutusCore.UPLC.Term.Program)
    (model : List String) (reverse := false) : Json :=
  replayWitness c left right model reverse

def replayOldAcceptance (c : Config) (left right : PlutusCore.UPLC.Term.Program)
    (model : List String) : Json :=
  replayWitness c left right model false true

private def replayConfirmed (witness : Json) : Bool :=
  (witness.getObjValAs? Bool "replayed").toOption == some true

/-- Call Blaster in-process on propositions constructed from decoded programs.
    Results are consumed as an inductive type, without parsing diagnostic text. -/
def solve (env : Environment) (c : Config) (left right : PlutusCore.UPLC.Term.Program)
    (checkedResults : Option (IO.Ref (Array (Option Blaster.Smt.Result))) := none)
    (diagnostics : Option (IO.Ref (Array (String × Json))) := none)
    (observer : Solver.Observer := {}) : IO (Array Blaster.Smt.Result) := do
  let progress := observer.message
  let programs := #[toExpr left, toExpr right]
  let plan := queries c
  let names := plan.map Query.name
  let skipRemaining := fun (checked : Nat) (reason : String) => do
    for pending in plan.toList.drop checked do
      progress s!"Skipping: {pending.name} ({reason})"
  let action : MetaM (Array Blaster.Smt.Result) := do
    let mut results := #[]
    let comparisonsProved := fun (checked : Array Blaster.Smt.Result) =>
      let result := fun name => checked[names.idxOf name]?.getD .Undetermined
      (result "acceptance_preserved" matches .Valid) &&
        (!c.equivalence || (result "reverse_acceptance_preserved" matches .Valid))
    for query in plan do
      if query.name == "old_rejected" && results.any (fun result => result matches .Falsified _) then
        -- A rejection proof cannot repair a disproved implication. Classification
        -- will report a replayed regression or an inconclusive comparison.
        skipRemaining results.size "comparison disproved"
        break
      if query.name == "old_rejected" && comparisonsProved results then
        progress "Starting: looking for an OLD-accepting replay"
        let witness := replayOldAcceptance c left right []
        if replayConfirmed witness then
          progress "Skipping: old_rejected (OLD acceptance confirmed by native replay)"
          if c.equivalence then progress "Skipping: new_rejected (both comparisons proved)"
          break
      if query.name == "new_rejected" && comparisonsProved results then
        progress "Skipping: new_rejected (both comparisons proved)"
        break
      if let some evidence := queryEvidence c query results then
        progress s!"Skipping: {query.name} (derived from {evidence})"
        results := results.push .Valid
        if let some ref := checkedResults then ref.modify (·.push none)
        continue
      progress s!"Starting: {query.description} [{query.name}]"
      observer.reportPhase "preprocessing" (some query.name)
      let primary ← Solver.runQuery (← queryProposition c query programs) query.name
        c.timeout query.wantsCounterexample diagnostics observer
      let mut combined := primary
      if checksLedger c && query.name == "old_rejected" &&
          comparisonsProved results && !(combined matches .Valid) then
        let model := match combined with
          | .Falsified model => model
          | _ => []
        unless replayConfirmed (replayOldAcceptance c left right model) do
          progress "Starting: synthesizing an OLD-accepting structured spending witness"
          let predicate ← queryPredicate c query programs
          let fast := c.maxInputs > 0 && c.maxOutputs > 0 && c.maxSigners > 0
          let (cpu, memory) := c.budget.getD (0, 0)
          let fastGoal := mkAppN (mkConst ``ValidContext.fastWitnessRejected)
            (query.sides.map (programs[·]!) ++ #[mkRawNatLit cpu, mkRawNatLit memory,
              toExpr true, toExpr c.bounded, toExpr c.budget.isSome, mkRawNatLit c.steps])
          for useFast in (if fast then [true, false] else [false]) do
            observer.reportPhase "preprocessing" (some "old_acceptance_witness_search")
            let goal ← if useFast then pure fastGoal else
              ValidContext.witnessProposition c.toLimits predicate
            let candidate ← Solver.runQuery goal
              "old_acceptance_witness_search" c.timeout true diagnostics observer
            if let .Falsified bindings := candidate then
              -- The search subset shares its output datum with the input.
              -- All other omitted fields use the same structured defaults.
              let sharedDatum := bindings.filterMap fun binding =>
                if binding.startsWith "datum: " then
                  some (": ".intercalate (binding.splitOn ": ").tail)
                else none
              let names := "input0Datum" :: (List.range c.maxOutputs).map (fun i => s!"output{i}Datum")
              let aliases := if useFast then
                bindings.filterMap (fun b => if b.startsWith "first: " then
                  some ("signer0: " ++ (": ".intercalate (b.splitOn ": ").tail)) else none) ++
                  ["input0Quantity: 1"] else []
              let bindings := bindings ++ aliases ++ sharedDatum.flatMap (fun value =>
                names.map fun name => name ++ ": " ++ value)
              if replayConfirmed (replayOldAcceptance c left right bindings) then
                combined := .Falsified bindings
                progress "Finished: ledger-valid OLD acceptance confirmed by native replay"
                break
              else progress "Finished: structured witness model failed validated replay"
            else
              -- Rejection on this search subset is not rejection on the domain.
              progress s!"Finished: structured witness search: {status candidate}"
      if let some ref := checkedResults then ref.modify (·.push (some primary))
      results := results.push combined
      progress s!"Finished: {query.name}: {status combined}"
      if c.mode == "validator" && query.sides.size == 2 then
        if let .Falsified model := combined then
          let witness := replayCounterexample c left right model (query.sides[0]? == some 1)
          if replayConfirmed witness then
            skipRemaining results.size "regression confirmed by native replay"
            break
      if (query.name == "old_rejected" || query.name == "new_rejected") && (combined matches .Valid) then
        for (previous, i) in (plan.toList.take results.size).zipIdx do
          if let some evidence := queryEvidence c previous results then
            results := results.set! i .Valid
            if let some ref := checkedResults then ref.modify (fun rows => rows.set! i none)
            progress s!"Derived: {previous.name} (from {evidence})"
    return results
  let (results, _) ← action.run' |>.toIO
    { fileName := "<uplc_equiv>", fileMap := default, maxRecDepth := 0, maxHeartbeats := 0 }
    { env }
  return results

def classifyFunction (c : Config) (results : Array Blaster.Smt.Result)
    (left right : PlutusCore.UPLC.Term.Program) : Json := Id.run do
  let result := results[0]?.getD .Undetermined
  let queryName := functionQueryName c
  let equivalent := if c.bounded then
    if c.equivalence then "bounded_equivalent" else "bounded_preserved"
    else "equivalent"
  let inequivalent := if c.bounded then
    if c.equivalence then "bounded_inequivalent" else "bounded_regression"
    else "inequivalent"
  let details := [("mode", toJson "function"), ("function_check", toJson (if c.bounded then if c.equivalence then "bounded_equivalence" else "bounded_preservation" else "strict")),
    ("check", toJson (if c.bounded then if c.equivalence then "bounded constant-or-none observation equality" else "OLD constant observations preserved by NEW within supplied limits" else "function outcome and returned-value equality")),
    ("input_domain", toJson (inputDomain c)), ("language", toJson c.language),
    ("budget", c.budget.map (fun (cpu, memory) => Json.mkObj [("cpu", toJson cpu), ("memory", toJson memory)]) |>.getD Json.null)] ++ c.stepLimitFields
  if left = right then
    return report equivalent "The decoded UPLC programs are identical; their behavior is identical for every input."
      (details ++ [("queries", Json.mkObj [("program_identity", toJson "valid"),
        (queryName, toJson "valid")]),
        ("derived_queries", Json.mkObj [(queryName, toJson "program_identity")]),
        ("verification", toJson "Decoded UPLC program equality; no SMT query required")])
  let details := details ++ [
    ("queries", Json.mkObj [(queryName, toJson (status result))]),
    ("verification", toJson "Blaster SMT result; no reconstructed Lean proof term")]
  match result with
  | .Valid =>
    let explanation := if c.bounded && !c.equivalence then
      "NEW preserves every constant result produced by OLD within the supplied limits; additional NEW results are allowed."
      else if c.bounded then
      "Both functions have equal constant-or-none observations within the supplied limits for every input; this does not establish unrestricted equivalence."
      else "Both functions return equal constants or both fail for every input in the declared domain."
    return report equivalent explanation details
  | .Falsified model =>
    let witness := replayCounterexample c left right model
    if replayConfirmed witness then
      return report inequivalent (if c.bounded then if c.equivalence then "The functions have different bounded observations on a replayed input." else "NEW fails to preserve an OLD constant result within the supplied limits on a replayed input." else "The functions produce different outcomes or returned values on a replayed input.")
        (details ++ [("counterexample", witness)])
    return report "inconclusive" "Function equivalence is unestablished: a limit, unsupported return value, or unreplayed countermodel prevented comparison."
      (details ++ [("diagnostic_counterexample", witness)])
  | .Undetermined => return report "inconclusive" "Function equivalence is unestablished: symbolic reasoning did not finish." details

def classify (c : Config) (results : Array Blaster.Smt.Result)
    (left right : PlutusCore.UPLC.Term.Program)
    (domainWitness : Option PlutusCore.Data.Data := none) : Json := Id.run do
  if c.mode == "function" then return classifyFunction c results left right
  let names := queryNames c
  let result := fun name => results[names.idxOf name]?.getD .Undetermined
  let mut ledgerFields := []
  if checksLedger c then
    let domainIssue := fun state message => report "inconclusive" message
      [("domain_status", toJson state), ("input_domain", toJson (inputDomain c))]
    match domainWitness with
      | some raw =>
        if !validLedgerContext c raw then return domainIssue "invalid_witness" "The supplied domain witness fails the ledger model."
        ledgerFields := [("domain_status", toJson "nonempty"),
          ("proof_domain", toJson "ledger-valid structured spending contexts"),
          ("domain_witness", PlutusCore.Data.toDetailedJson raw), ("ledger_validity", auditLedgerContext c raw)]
      | _ => return domainIssue "unestablished" "Could not construct a ledger-valid context witnessing the selected domain; no preservation claim is made."
  let mismatch := result "no_acceptance_regression"
  let preserved := result "acceptance_preserved"
  let reverseMismatch := result "reverse_no_acceptance_regression"
  let reversePreserved := result "reverse_acceptance_preserved"
  -- Prefer a forward witness when both directions expose a regression.
  let replayedDifference := fun (result : Blaster.Smt.Result) (reverse : Bool) => match result with
    | .Falsified model =>
      let witness := replayCounterexample c left right model reverse
      if replayConfirmed witness then some (reverse, model) else none
    | _ => none
  let regression := match mismatch, reverseMismatch with
    | .Falsified model, _ => some (false, model)
    | _, .Falsified model => if c.equivalence then some (true, model) else none
    | _, _ => (replayedDifference preserved false).orElse fun _ =>
        if c.equivalence then replayedDifference reversePreserved true else none
  let complete := (preserved matches .Valid) && (!c.equivalence || (reversePreserved matches .Valid))
  let boundedPrefix := if c.bounded then "bounded_" else ""
  let successVerdict := boundedPrefix ++ if c.equivalence then "equivalent" else "preserved"
  let failureVerdict := boundedPrefix ++ if c.equivalence then "inequivalent" else "regression"
  let scope := if c.bounded then "within the supplied step and optional execution-budget limits" else "under the supplied budget"
  let (initialVerdict, initialExplanation) :=
    if regression.isSome then
      if c.equivalence then (failureVerdict, s!"One script accepts an input not accepted by the other {scope}.")
      else (failureVerdict, s!"An input accepted by OLD is not accepted by NEW {scope}.")
    else if complete then
      if c.equivalence then (successVerdict, s!"Both scripts accept the same inputs in the declared domain {scope}.")
      else (successVerdict, s!"NEW accepts every input accepted by OLD in the declared domain {scope}.")
    else ("inconclusive", "Acceptance preservation is unestablished: analysis or symbolic reasoning did not finish.")
  let mut verdict := initialVerdict
  let mut explanation := initialExplanation
  let mut acceptanceFields := []
  let (cpu, memory) := c.budget.getD (0, 0)
  if complete && regression.isNone then
    match result "old_rejected" with
    | .Valid =>
      verdict := "vacuously_" ++ successVerdict
      explanation := s!"OLD accepts no input in the declared domain {scope}; preservation is vacuous."
      let variant : PlutusCore.Default.BuiltinSemanticsVariant := if c.language == "PlutusV3" then
        .defaultFunSemanticsVariantE else .defaultFunSemanticsVariantD
      let costs := PlutusCore.UPLC.CekMachine.semVarToCosts variant
      let startup := costs.startupCost
      let budget : PlutusCore.UPLC.ExBudget.ExBudget := ⟨⟨cpu⟩, ⟨memory⟩⟩
      let belowStartup := c.budget.isSome && !budget.canAfford startup
      -- Every supported domain supplies at least one argument, hence its initial
      -- term is an application, independent of the script and input values.
      let belowFirstStep := c.budget.isSome && !budget.canAfford (startup + costs.stepCostApply)
      if belowStartup then
        explanation := "The supplied budget cannot cover startup; OLD and NEW reject every input before execution. Preservation is vacuous."
      else if belowFirstStep then
        explanation := "The supplied budget covers startup but cannot cover the first application step; OLD and NEW reject every input. Preservation is vacuous."
      acceptanceFields := [("old_acceptance_status", toJson "rejected_everywhere"),
        ("vacuity_reason", toJson (if belowStartup then "startup_budget_exhausted"
          else if belowFirstStep then "initial_step_budget_exhausted"
          else if c.bounded then "old_rejects_bounded_domain" else "old_rejects_domain"))]
    | rejectionResult =>
      let model := match rejectionResult with
        | .Falsified model => model
        | _ => []
      let witness := replayOldAcceptance c left right model
      if replayConfirmed witness then
        acceptanceFields := [("old_acceptance_status", toJson "accepted"),
          ("old_acceptance_witness", witness)]
      else
        verdict := "inconclusive"
        explanation := s!"Preservation was proved, but no input accepted by OLD could be established in the declared domain {scope}."
        acceptanceFields := [("old_acceptance_status", toJson "unestablished"),
          ("inconclusive_reason", toJson "old_acceptance_unestablished"),
          ("diagnostic_old_acceptance", witness)]
  let details := [
    ("mode", toJson "validator"),
    ("check", toJson (if c.equivalence then "acceptance preservation in both directions" else "old acceptance implies new acceptance")),
    ("budget", c.budget.map (fun (cpu, memory) => Json.mkObj [("cpu", toJson cpu), ("memory", toJson memory)]) |>.getD Json.null),
    ("language", toJson c.language)] ++ c.stepLimitFields ++
    [("context_limits", Json.mkObj [
      ("inputs_min", toJson (0 : Nat)), ("inputs_max", toJson c.maxInputs),
      ("outputs_min", toJson (0 : Nat)), ("outputs_max", toJson c.maxOutputs),
      ("signers_max", toJson c.maxSigners), ("integer_bits", Json.null),
      ("inspected_byte_string_bytes", Json.null),
      ("value_policy_entries", toJson (2 : Nat)), ("tokens_per_policy", toJson (1 : Nat)),
      ("script_purpose", toJson "spending"), ("validity_range", toJson "arbitrary Data")])] ++
    (if c.budget.isSome then [("cost_model", toJson (if c.language == "PlutusV3" then "bundled post-Conway E" else "bundled post-Conway D"))]
     else [("execution", toJson "uncosted")])
  let counterexample := regression.toList.map fun (reverse, model) =>
    ("counterexample", replayCounterexample c left right model reverse)
  if checksLedger c then
    for (_, witness) in counterexample do
      unless replayConfirmed witness do
        return report "inconclusive" "The symbolic countermodel could not be replayed as a ledger-valid acceptance regression."
          (ledgerFields ++ [("input_domain", toJson (inputDomain c)), ("diagnostic_counterexample", witness)])
  let derivations := (queries c).toList.filterMap fun query =>
    (queryEvidence c query results).map fun evidence => (query.name, toJson evidence)
  let provenance := if derivations.isEmpty then [] else [("derived_queries", Json.mkObj derivations)]
  return report verdict explanation ([("input_domain", toJson (inputDomain c))] ++ details ++ ledgerFields ++ acceptanceFields ++ [
    ("queries", Json.mkObj (names.toList.zip (results.toList.map (toJson ∘ status)))),
    ("verification", toJson "Blaster SMT result; no reconstructed Lean proof term")] ++ provenance ++ counterexample)

/-- Check two decoded programs. Observers are optional; library checks are silent
    by default. inspectQueries can export or inspect the initial and checked plan. -/
def check (c : Config) (left right : PlutusCore.UPLC.Term.Program)
    (observer : Solver.Observer := {})
    (inspectQueries : Environment → Array (Option Blaster.Smt.Result) → IO Unit := fun _ _ => pure ()) : IO Json := do
  IO.ofExcept c.validate
  let progress := observer.message
  observer.reportPhase "preprocessing"
  if c.mode == "function" && decide (left = right) then
    progress "Finished: program_identity: identical decoded UPLC programs"
    return classifyFunction c #[] left right
  observer.reportPhase "validation"
  if checksLedger c then progress "Starting: constructing a ledger-model-valid domain witness"
  let domainWitness := if checksLedger c then nativeDomainWitness c else none
  if checksLedger c && domainWitness.isNone then
    return report "inconclusive" "Could not construct a ledger-valid context witnessing the selected domain; no preservation claim is made."
      [("domain_status", toJson "unestablished"), ("input_domain", toJson (inputDomain c))]
  if checksLedger c then progress "Finished: ledger-model-valid domain witness constructed"
  -- Resolve dependencies when the checker is used outside Lake or the repository.
  progress "Starting: preparing symbolic checker"
  observer.reportPhase "preprocessing"
  initSearchPath toolchainRoot (moduleSearchPath.map FilePath.mk)
  let env ← importModules #[{ module := `Equivalence.Queries }, { module := `Equivalence.ValidContext }, { module := `Blaster }] {} (loadExts := true)
  inspectQueries env #[]
  let checkedResults ← IO.mkRef #[]
  let diagnostics ← IO.mkRef #[]
  if c.skipOldRejected then progress "Skipping: old_rejected (--skip-old-rejected)"
  let results ← solve env c left right (some checkedResults) (some diagnostics) observer
  inspectQueries env (← checkedResults.get)
  progress "Starting: validating replay witnesses and classifying results"
  observer.reportPhase "validation"
  let result := classify c results left right domainWitness
  let diagnostics ← diagnostics.get
  return if diagnostics.isEmpty then result else
    result.setObjVal! "query_diagnostics" (Json.mkObj diagnostics.toList)

end Equivalence.Checker
