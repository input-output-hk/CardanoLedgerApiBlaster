import Equivalence.Queries
import PlutusCore.Smt.Model
import Equivalence.ValidContextModel
import Equivalence.Solver
import Equivalence.Dispatch.Discover
import Equivalence.Dispatch.Partition

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
  purpose : String := "spend"
  bounded : Bool := false
  steps : Nat := 100000
  language : String := "PlutusV3"
  languageOld : Option String := none
  languageNew : Option String := none
  inputs : String := "valid-context"
  equivalence : Bool := false
  budget : Option (Nat × Nat) := none
  timeout : Nat := 20
  solverJobs : Nat := 1
  solverSeed : Option Nat := none
  skipOldRejected : Bool := false
  /-- Equality-guided exhaustive proof partition before unrestricted fallback queries. -/
  splitDispatch : Bool := false
  dispatchCaseLimit : Nat := 16
  dispatchTimeout : Nat := 10

def Config.languageFor (c : Config) (side : Nat) : String :=
  (if side == 0 then c.languageOld else c.languageNew).getD c.language

def Config.isV3 (c : Config) (side : Nat) : Bool := c.languageFor side == "PlutusV3"

def Config.mixedLanguages (c : Config) : Bool := c.languageFor 0 != c.languageFor 1

def Config.minting (c : Config) : Bool := c.purpose == "mint"

def Config.withdrawal (c : Config) : Bool := c.purpose == "withdraw"

def Config.spending (c : Config) : Bool := c.purpose == "spend"

def Config.versionedArguments (c : Config) : Bool := c.mixedLanguages || !c.spending

def Config.rejectionDeclaration (c : Config) : Name :=
  if c.minting then ``Queries.mintingRejected
  else if c.withdrawal then ``Queries.withdrawalRejected
  else if c.mixedLanguages then ``Queries.spendingRejected
  else ``Queries.rejected

def Config.languageFields (c : Config) : List (String × Json) :=
  if c.mixedLanguages then
    [("language_old", toJson (c.languageFor 0)), ("language_new", toJson (c.languageFor 1))]
  else [("language", toJson (c.languageFor 0))]

/-- Steps restrict execution in bounded mode; otherwise they only guard analysis. -/
def Config.stepLimitFields (c : Config) : List (String × Json) := [
  ("solver_seed", toJson (c.solverSeed.getD 0)), ("solver_workers", toJson c.solverJobs),
  ("steps", toJson c.steps), ("bounded", toJson c.bounded),
  ("step_limit_kind", toJson (if c.bounded then "execution_bound" else "analysis_guard"))] ++
  (c.datum.map (fun datum => [("fixed_datum", PlutusCore.Data.toDetailedJson datum)])).getD [] ++
  (c.redeemer.map (fun redeemer => [("fixed_redeemer", PlutusCore.Data.toDetailedJson redeemer)])).getD []

/-- Check semantic option combinations for library callers as well as the CLI. -/
def Config.validate (c : Config) : Except String Unit := do
  unless ["validator", "function"].contains c.mode do throw s!"unsupported mode: {c.mode}"
  unless ["spend", "mint", "withdraw"].contains c.purpose do throw s!"unsupported purpose: {c.purpose}"
  if c.dispatchTimeout == 0 then throw "dispatch case timeout must be positive"
  if c.dispatchCaseLimit == 0 then throw "dispatch case limit must be positive"
  if c.steps == 0 then throw "step limit must be positive"
  if c.timeout == 0 then throw "solver timeout must be positive"
  if c.solverJobs == 0 then throw "solver worker count must be positive"
  if c.solverSeed.getD 0 + c.solverJobs - 1 > 4294967295 then
    throw "solver seeds must fit in an unsigned 32-bit integer"
  for language in [c.language, c.languageFor 0, c.languageFor 1] do
    unless ["PlutusV1", "PlutusV2", "PlutusV3"].contains language do
      throw s!"unsupported language: {language}"
  if c.mode == "validator" && !c.bounded && c.budget.isNone then
    throw "validator checking requires --budget CPU MEMORY or --bounded --steps N"
  if c.mode == "function" then
    unless c.spending do throw s!"--purpose {c.purpose} requires validator mode"
    if c.mixedLanguages then throw "function comparison requires matching languages"
    if c.maxEarlierSpendingRedeemers != 0 then throw "earlier spending redeemer limit is a validator option"
    if c.splitDispatch then throw "--split-dispatch is a validator option"
    if c.datum.isSome then throw "--datum is a validator option"
    if c.redeemer.isSome then throw "--redeemer is a validator option"
    unless ["integer", "data", "data3"].contains c.inputs do
      throw "function mode supports --inputs integer, data or data3"
    if c.equivalence && !c.bounded then
      throw "function --equivalence requires --bounded; strict function mode already compares both outcomes"
    if c.skipOldRejected then
      throw "--skip-old-rejected is a validator option"
  if c.mode == "validator" then
    if c.inputs != "valid-context" then
      throw s!"unsupported validator input mode: {c.inputs}; use valid-context"
    if !c.spending then
      unless [c.languageFor 0, c.languageFor 1].all (fun lang => ["PlutusV2", "PlutusV3"].contains lang) do
        throw s!"--purpose {c.purpose} requires PlutusV2 or PlutusV3"
      if c.datum.isSome then throw "--datum requires --purpose spend"
      if c.maxEarlierSpendingRedeemers != 0 then
        throw "--max-earlier-spending-redeemers requires --purpose spend"
      if c.splitDispatch then throw "--split-dispatch requires --purpose spend"
    else if c.mixedLanguages then
      unless [c.languageFor 0, c.languageFor 1].contains "PlutusV2" &&
          [c.languageFor 0, c.languageFor 1].contains "PlutusV3" do
        throw "mixed-language spending checks require PlutusV2 and PlutusV3"
      if c.splitDispatch then throw "--split-dispatch requires two PlutusV3 validators"
    else unless c.isV3 0 do throw "same-language spending checks require PlutusV3"

def checksLedger (c : Config) : Bool := c.mode == "validator"

def validLedgerContext (c : Config) (raw : PlutusCore.Data.Data) : Bool :=
  if c.minting then
    ValidContext.containsMinting c.toLimits raw &&
      Context.validMintingArguments (!c.isV3 0 || !c.isV3 1) (c.isV3 0 || c.isV3 1) (Queries.contextArgs raw)
  else if c.withdrawal then
    ValidContext.containsWithdrawal c.toLimits raw &&
      Context.validWithdrawalArguments (!c.isV3 0 || !c.isV3 1) (c.isV3 0 || c.isV3 1) (Queries.contextArgs raw)
  else (if c.mixedLanguages then Context.validSharedArguments (Queries.contextArgs raw)
    else Ledger.validContext raw) && ValidContext.contains c.toLimits raw

def auditLedgerContext (c : Config) (raw : PlutusCore.Data.Data) : Json :=
  if !c.spending then
    let predicate := if c.minting then "validMintingContext" else "validRewardingContext"
    Json.mkObj [("predicate", toJson s!"{predicate} ({c.languageFor 0}, {c.languageFor 1})"),
      ("valid", toJson (validLedgerContext c raw))]
  else if c.mixedLanguages then Json.mkObj [
    ("predicate", toJson "V2 and V3 validSpendingContext"),
    ("valid", toJson (Context.validSharedArguments (Queries.contextArgs raw)))]
  else Ledger.audit raw

/-- One query description drives solving, reports and emitted Lean source.
    Side indices select the OLD (0) or NEW (1) program. -/
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
    let (noRegression, preserved) := if c.minting then
        (``Queries.mintingNoAcceptanceRegression, ``Queries.mintingAcceptancePreserved)
      else if c.withdrawal then
        (``Queries.withdrawalNoAcceptanceRegression, ``Queries.withdrawalAcceptancePreserved)
      else if c.mixedLanguages then
        (``Queries.spendingNoAcceptanceRegression, ``Queries.spendingAcceptancePreserved)
      else (``Queries.noAcceptanceRegression, ``Queries.acceptancePreserved)
    let forward : Array Query := #[
      ⟨"acceptance_preserved", preserved, #[0, 1]⟩,
      ⟨"no_acceptance_regression", noRegression, #[0, 1]⟩]
    let rejected := fun (name : String) (side : Nat) =>
      #[Query.mk name c.rejectionDeclaration #[side]]
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
  if c.minting then
    s!"Structured minting transactions for OLD {c.languageFor 0} and NEW {c.languageFor 1}, with up to {c.maxInputs} inputs, {c.maxOutputs} outputs and {c.maxSigners} signers. The policy currency symbol, one token name and its nonzero mint or burn quantity are symbolic. The redeemer map contains the current minting entry. Inputs and outputs follow the spending profile's value and address shapes. Reference inputs, certificates, withdrawals and governance fields are empty or absent. Transactions satisfy the selected ledger models." ++
    (c.redeemer.map (fun redeemer => s!" Restricted to redeemer {redeemer}.")).getD ""
  else if c.withdrawal then
    s!"Structured reward-withdrawal transactions for OLD {c.languageFor 0} and NEW {c.languageFor 1}, with up to {c.maxInputs} inputs, {c.maxOutputs} outputs and {c.maxSigners} signers. One symbolic script credential withdraws a nonnegative amount of lovelace, including zero. The redeemer map contains the current withdrawal entry. Inputs and outputs follow the spending profile's value and address shapes. Reference inputs, certificates, and governance fields are empty or absent. Transactions satisfy the selected ledger models." ++
    (c.redeemer.map (fun redeemer => s!" Restricted to redeemer {redeemer}.")).getD ""
  else if c.mode == "validator" then
    (if c.mixedLanguages then
      s!"Shared spending transactions for OLD {c.languageFor 0} and NEW {c.languageFor 1}, with "
    else "Structured V3 spending contexts with ") ++
    s!"0..{c.maxInputs} independently symbolic inputs, 0..{c.maxOutputs} outputs and 0..{c.maxSigners} signer byte strings; present script datum; typed independent input and spending references; input pubkey/script credentials without staking and absent/hash/inline datums; outputs have arbitrary addresses and inline datums; no reference scripts; each value has an ADA entry and one independent policy/token entry; arbitrary Data validity range, datum and redeemer; 0..{c.maxEarlierSpendingRedeemers} spending redeemers before the current map entry" ++
    (if c.mixedLanguages then
      "; no later redeemers, reference inputs, certificates, withdrawals or governance fields; shared fee, mint, datum map and transaction ID; both ledger models must validate the spend"
    else " and a symbolic tail; other auxiliary fields are arbitrary Data; symbolic queries require CardanoLedgerApi.V3.validSpendingContext") ++
    "; unbounded integers and byte strings; concrete witnesses and counterexamples are independently ledger-validated and natively replayed; model validity does not establish on-chain reachability" ++
    (c.datum.map (fun datum => s!"; restricted to spending datum {datum}")).getD "" ++
    (c.redeemer.map (fun redeemer => s!"; restricted to spending redeemer {redeemer}")).getD ""
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
    let raw ← if c.minting then ValidContext.validMintingContext c.toLimits
      else if c.withdrawal then ValidContext.validWithdrawalContext c.toLimits
      else ValidContext.validContext c.toLimits
    if validLedgerContext c raw then some raw else none
  else none

/-- Construct the per-argument property independently of context enumeration. -/
def queryPredicate (c : Config) (query : Query) (programs : Array Expr) : MetaM Expr := do
  let (cpu, memory) := c.budget.getD (0, 0)
  let sides := if c.versionedArguments then query.sides else #[0]
  let limits := #[mkRawNatLit cpu, mkRawNatLit memory] ++ sides.map (toExpr ∘ c.isV3)
  if c.mode == "function" then
    return mkAppN (mkConst query.declaration) (query.sides.map (programs[·]!) ++
      limits ++ #[toExpr c.budget.isSome, mkRawNatLit c.steps])
  Meta.withLocalDeclD `args (mkApp (mkConst ``List [.zero])
      (mkConst ``PlutusCore.UPLC.Term.Term)) fun args => do
    let body := mkAppN (mkConst query.declaration) (#[args] ++ query.sides.map (programs[·]!) ++
      limits ++ #[toExpr c.bounded, toExpr c.budget.isSome, mkRawNatLit c.steps])
    let valid := if !c.spending then
        let predicate := if c.minting then ``Context.validMintingArguments else ``Context.validWithdrawalArguments
        mkApp3 (mkConst predicate) (toExpr (!c.isV3 0 || !c.isV3 1)) (toExpr (c.isV3 0 || c.isV3 1)) args
      else mkApp (mkConst (if c.mixedLanguages then
        ``Context.validSharedArguments else ``Ledger.validArguments)) args
    let premise ← Meta.mkEq valid (toExpr true)
    -- Establish ledger validity before specializing either script. In particular,
    -- invalid zero-input frames must not expand the symbolic CEK execution.
    let guarded ← mkArrow premise body
    Meta.mkLambdaFVars #[args] guarded

def queryProposition (c : Config) (query : Query) (programs : Array Expr) : MetaM Expr := do
  let predicate ← queryPredicate c query programs
  if c.mode == "function" then return predicate
  ValidContext.proposition c.toLimits predicate (shared := c.mixedLanguages)
    (minting := c.minting) (withdrawal := c.withdrawal)

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

private def scriptArguments (c : Config) (side : Nat) (args : List PlutusCore.UPLC.Term.Term) :
    List PlutusCore.UPLC.Term.Term :=
  if c.minting then Context.mintingArguments (c.isV3 side) args
  else if c.withdrawal then Context.withdrawalArguments (c.isV3 side) args
  else if c.mixedLanguages then Context.spendingArguments (c.isV3 side) args
  else args

private def validatorArgumentFields (c : Config) (args : List PlutusCore.UPLC.Term.Term) :
    List (String × Json) :=
  if c.versionedArguments then
    let encoded := fun side =>
      (scriptArguments c side args).filterMap fun
        | .Const (.Data value) => some (PlutusCore.Data.toDetailedJson value)
        | _ => none
    [("arguments", Json.mkObj [("old", toJson (encoded 0)), ("new", toJson (encoded 1))])]
  else []

def replayWitness (c : Config) (oldProgram newProgram : PlutusCore.UPLC.Term.Program)
    (model : List String) (reverse := false) (acceptanceOnly := false) : Json := Id.run do
  let (cpu, memory) := c.budget.getD (0, 0)
  let replay := fun args input => do
    let execute := fun side program =>
      let scriptArgs := scriptArguments c side args
      Function.execute program scriptArgs cpu memory (c.isV3 side) c.budget.isSome c.steps
    let old := execute 0 oldProgram
    let new := execute 1 newProgram
    let oldObserved := Function.observeValidator c.bounded old
    let newObserved := Function.observeValidator c.bounded new
    let reproduces := if c.mode == "function" then
        if c.bounded then
          if c.equivalence then !Function.boundedSame old new else !Function.boundedPreserved old new
        else Function.same old new == some false
      else
        let oldAccepts := Acceptance.accepts (c.isV3 0) oldObserved
        let newAccepts := Acceptance.accepts (c.isV3 1) newObserved
        if acceptanceOnly then oldAccepts == some true
        else if reverse then newAccepts == some true && oldAccepts == some false
        else oldAccepts == some true && newAccepts == some false
    if reproduces then
      let outcome := fun side => if c.mode == "function" then functionOutcomeJson c.budget.isSome
        else fun result => budgetOutcomeJson (c.isV3 side) result c.bounded c.budget.isSome
      let validity := if c.mode == "function" then [] else match args with
        | [.Const (.Data context)] => [("ledger_validity", auditLedgerContext c context)]
        | _ => []
      some (Json.mkObj ([("input", input), ("old", outcome 0 old),
        ("new", outcome 1 new),
        ("direction", toJson (if c.mode == "function" then "function_outcomes" else if acceptanceOnly then "old_acceptance" else if reverse then "new_to_old" else "old_to_new")),
        ("replayed", toJson true)] ++ validity ++ validatorArgumentFields c args))
    else none
  let replayContext := fun args => do
    let [.Const (.Data context)] := args | none
    if checksLedger c && !validLedgerContext c context then none
    else replay args (PlutusCore.Data.toDetailedJson context)
  -- Optimization can reduce a universally false query to False without asking
  -- Z3 for a model. Try zero inputs too, but still require a successful replay.
  if checksLedger c then
    for context in ValidContext.modelContexts c.toLimits model c.minting c.withdrawal ++
        ValidContext.modelContexts c.toLimits [] c.minting c.withdrawal do
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

def replayCounterexample (c : Config) (oldProgram newProgram : PlutusCore.UPLC.Term.Program)
    (model : List String) (reverse := false) : Json :=
  replayWitness c oldProgram newProgram model reverse

def replayOldAcceptance (c : Config) (oldProgram newProgram : PlutusCore.UPLC.Term.Program)
    (model : List String) : Json :=
  replayWitness c oldProgram newProgram model false true

private def replayConfirmed (witness : Json) : Bool :=
  (witness.getObjValAs? Bool "replayed").toOption == some true

/-- Keep goal construction, speculative search and proof queries on the same
    deadline and error policy. -/
private def runDispatchQuery (c : Config) (goal : MetaM Expr) (name : String)
    (diagnostics : Option (IO.Ref (Array (String × Json)))) (observer : Solver.Observer) :
    MetaM (Blaster.Smt.Result × String) := do
  try
    match ← Solver.runQueryTimed (← getEnv) goal name c.timeout c.dispatchTimeout
        diagnostics observer c.solverJobs c.solverSeed with
    | some result => pure (result, status result)
    | none => pure (.Undetermined, "case_timeout")
  catch error =>
    observer.message s!"Dispatch case could not be checked [{name}]: {← error.toMessageData.toString}"
    pure (.Undetermined, "error")

/-- Discovered cases are search subsets, not an exhaustive proof partition.
A result is promoted to the original domain only after independent native replay.
An unsuccessful search is followed by an exhaustive proof partition. -/
private def searchDispatch (c : Config) (oldProgram newProgram : PlutusCore.UPLC.Term.Program)
    (programs : Array Expr) (discovery : Dispatch.Discovery) (info : Option (IO.Ref Json))
    (diagnostics : Option (IO.Ref (Array (String × Json)))) (observer : Solver.Observer) : MetaM (Option (Array Blaster.Smt.Result)) := do
  let plan := queries c
  let mut tried : Array Json := #[]
  let summary := fun (tried : Array Json) winner => Json.mkObj [
    ("strategy", toJson "equality-guided subset search"),
    ("discovered_cases", toJson discovery.cases.size), ("discovery_limited", toJson discovery.limited),
    ("discovery_limits", toJson discovery.limitReasons),
    ("facts", toJson discovery.factCount), ("cases", toJson tried),
    ("winning_case", winner), ("proof_fallback", toJson "original full domain")]
  observer.message s!"Dispatch discovery: {discovery.cases.size} cases, {discovery.factCount} facts{if discovery.limited then " (discovery limit reached: " ++ String.intercalate ", " discovery.limitReasons.toList ++ ")" else ""}"
  for (candidate, index) in discovery.cases.zipIdx do
    let mut outcomes := []
    let label := s!"dispatch_{index}"
    let caseReport := fun outcomes extra => Json.mkObj ([
      ("id", toJson index), ("datum", toJson candidate.datum.describe),
      ("redeemer", toJson candidate.redeemer.describe), ("exclusions", toJson candidate.exclusions),
      ("queries", Json.mkObj outcomes)] ++ extra)
    let replayModel := fun bindings reverse => do
      let model ← candidate.model bindings
      let probe := { c with
        datum := candidate.datum.value "dispatch_datum" bindings
        redeemer := candidate.redeemer.value "dispatch_redeemer" bindings }
      if replayConfirmed (replayCounterexample probe oldProgram newProgram model reverse) then some model else none
    observer.message s!"Starting: {label}: {candidate.describe}"
    for (query, queryIndex) in plan.zipIdx do
      unless query.name.endsWith "no_acceptance_regression" do continue
      let name := label ++ "_" ++ query.name
      -- Literal/shape dispatch can already distinguish the scripts on a valid
      -- default context. Z3 is needed only when other fields must be discovered.
      if let some model := replayModel [] (query.sides[0]? == some 1) then
        let record := caseReport (outcomes ++ [(query.name, toJson "native_falsified")])
          [("replayed", toJson true), ("native_probe", toJson true)]
        tried := tried.push record
        if let some ref := info then ref.set (summary tried record)
        observer.message s!"Finished: {name}: native probe confirmed a regression in the original domain"
        return some ((Array.replicate plan.size (.Undetermined : Blaster.Smt.Result)).set! queryIndex (.Falsified model))
      let goal := do
        let predicate ← queryPredicate c query programs
        candidate.proposition c.toLimits predicate
      let (result, resultStatus) ← runDispatchQuery c goal name diagnostics observer
      outcomes := outcomes ++ [(query.name, toJson resultStatus)]
      if let .Falsified bindings := result then
        if let some model := replayModel bindings (query.sides[0]? == some 1) then
          let record := caseReport outcomes [("replayed", toJson true)]
          tried := tried.push record
          if let some ref := info then ref.set (summary tried record)
          observer.message s!"Finished: {name}: regression confirmed by native replay in the original domain"
          let results := (Array.replicate plan.size (.Undetermined : Blaster.Smt.Result)).set! queryIndex (.Falsified model)
          return some results
        observer.message s!"Finished: {name}: countermodel did not pass strict decoding and native replay"
    tried := tried.push (caseReport outcomes [])
    if let some ref := info then ref.set (summary tried Json.null)
  if let some ref := info then ref.set (summary tried Json.null)
  observer.message "Dispatch search did not establish a difference; checking an exhaustive proof partition"
  return none

/-- Every discovered guard is checked on the original context schema, excluding
previous guards. The final part is their complement. Discovery limits therefore
cannot omit inputs from a proof. Counterexamples still require native replay. -/
private def proveDispatch (c : Config) (oldProgram newProgram : PlutusCore.UPLC.Term.Program)
    (programs : Array Expr) (discovery : Dispatch.Discovery) (info : Option (IO.Ref Json))
    (diagnostics : Option (IO.Ref (Array (String × Json)))) (observer : Solver.Observer) :
    MetaM (Array (Option Blaster.Smt.Result) × Option (List String)) := do
  let plan := queries c
  let comparisons := plan.zipIdx.filter (fun (query, _) => query.name.endsWith "acceptance_preserved")
  let mut cached : Array (Option Blaster.Smt.Result) := Array.replicate plan.size none
  let mut oldAcceptanceModel : Option (List String) := none
  let mut allValid := Array.replicate plan.size true
  let mut tried : Array Json := #[]
  let previous ← match info with | some ref => ref.get | none => pure Json.null
  let searchCases := (previous.getObjVal? "cases").toOption.getD (toJson (#[] : Array Json))
  let summary := fun (tried : Array Json) (winner : Json) (proved : Array String) (fallback : Bool) => Json.mkObj [
    ("strategy", toJson "exhaustive equality-guided partition"),
    ("discovered_cases", toJson discovery.cases.size), ("discovery_limited", toJson discovery.limited),
    ("discovery_limits", toJson discovery.limitReasons),
    ("facts", toJson discovery.factCount), ("cases", toJson tried), ("search_cases", searchCases),
    ("partition_cases", toJson (discovery.cases.size + 1)), ("exhaustive", toJson true),
    ("proved_queries", toJson (proved : Array String)), ("winning_case", winner),
    ("proof_fallback", toJson (if fallback then "original full domain" else "not needed"))]
  observer.message s!"Dispatch proof partition: {discovery.cases.size + 1} cases, including the catch-all"
  for index in [:discovery.cases.size + 1] do
    let candidate := discovery.cases[index]?
    let label := if candidate.isSome then s!"dispatch_{index}" else "dispatch_catch_all"
    let mut outcomes := []
    let caseReport := fun outcomes extra => Json.mkObj ([
      ("id", toJson index), ("catch_all", toJson candidate.isNone),
      ("datum", toJson ((candidate.map (·.datum.describe)).getD "?Data")),
      ("redeemer", toJson ((candidate.map (·.redeemer.describe)).getD "?Data")),
      ("exclusions", toJson ((candidate.map Dispatch.Case.exclusions).getD [])),
      ("excludes_previous_cases", toJson index),
      ("queries", Json.mkObj outcomes)] ++ extra)
    -- An accepting discovered input also settles nonvacuity, independently of
    -- whether that case is useful for proving preservation.
    if oldAcceptanceModel.isNone then
      if let some model := candidate.bind (·.model []) then
        if replayConfirmed (replayOldAcceptance c oldProgram newProgram model) then
          oldAcceptanceModel := some model
    observer.message s!"Starting: {label}: {(candidate.map Dispatch.Case.describe).getD "all inputs not covered by earlier cases"}"
    for (query, queryIndex) in comparisons do
      let name := label ++ "_" ++ query.name
      let goal := do
        let predicate ← queryPredicate c query programs
        Dispatch.partitionProposition discovery.cases index c.toLimits predicate
      let (result, resultStatus) ← runDispatchQuery c goal name diagnostics observer
      outcomes := outcomes ++ [(query.name, toJson resultStatus)]
      unless result matches .Valid do allValid := allValid.set! queryIndex false
      if let .Falsified model := result then
        if replayConfirmed (replayCounterexample c oldProgram newProgram model (query.sides[0]? == some 1)) then
          let record := caseReport outcomes [("replayed", toJson true)]
          tried := tried.push record
          if let some ref := info then ref.set (summary tried record #[] false)
          observer.message s!"Finished: {name}: regression confirmed by native replay in the original domain"
          return ((Array.replicate plan.size none).set! queryIndex (some (.Falsified model)),
            oldAcceptanceModel)
        observer.message s!"Finished: {name}: countermodel did not pass strict decoding and native replay"
    tried := tried.push (caseReport outcomes [])
    if let some ref := info then ref.set (summary tried Json.null #[] true)
  let mut proved := #[]
  for (query, index) in comparisons do
    if allValid[index]! then
      cached := cached.set! index (some .Valid)
      proved := proved.push query.name
  let complete := proved.size == comparisons.size
  if let some ref := info then ref.set (summary tried Json.null proved (!complete))
  if complete then observer.message "Dispatch partition proved every preservation direction over the original full domain"
  else observer.message "Dispatch partition proof incomplete; checking remaining queries over the original full domain"
  if let some oldIndex := plan.findIdx? (·.name == "old_rejected") then
    cached := cached.set! oldIndex (oldAcceptanceModel.map Blaster.Smt.Result.Falsified)
  return (cached, oldAcceptanceModel)

private def synthesizeOldAcceptance (c : Config)
    (oldProgram newProgram : PlutusCore.UPLC.Term.Program) (programs : Array Expr)
    (diagnostics : Option (IO.Ref (Array (String × Json)))) (observer : Solver.Observer) :
    MetaM (Option (List String)) := do
  let progress := observer.message
  let query : Query := ⟨"old_rejected", c.rejectionDeclaration, #[0]⟩
  progress "Starting: synthesizing an OLD-accepting witness"
  if !c.spending then
    observer.reportPhase "preprocessing" (some "old_acceptance_witness_search")
    let goal ← queryProposition c query programs
    let result ← Solver.runQuery goal "old_acceptance_witness_search" c.timeout true diagnostics
      observer c.solverJobs c.solverSeed
    if let .Falsified bindings := result then
      if replayConfirmed (replayOldAcceptance c oldProgram newProgram bindings) then return some bindings
    return none
  let predicate ← queryPredicate c query programs
  let fast := !c.mixedLanguages && c.datum.isNone && c.redeemer.isNone &&
    c.maxInputs > 0 && c.maxOutputs > 0 && c.maxSigners > 0
  let (cpu, memory) := c.budget.getD (0, 0)
  let fastGoal := mkAppN (mkConst ``ValidContext.fastWitnessRejected)
    (query.sides.map (programs[·]!) ++ #[mkRawNatLit cpu, mkRawNatLit memory,
      toExpr true, toExpr c.bounded, toExpr c.budget.isSome, mkRawNatLit c.steps])
  for useFast in (if fast then [true, false] else [false]) do
    observer.reportPhase "preprocessing" (some "old_acceptance_witness_search")
    let goal ← if useFast then pure fastGoal else
      ValidContext.witnessProposition c.toLimits predicate
    let candidate ← Solver.runQuery goal
      "old_acceptance_witness_search" c.timeout true diagnostics observer c.solverJobs c.solverSeed
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
      if replayConfirmed (replayOldAcceptance c oldProgram newProgram bindings) then
        progress "Finished: ledger-valid OLD acceptance confirmed by native replay"
        return some bindings
      else progress "Finished: structured witness model failed validated replay"
    else
      -- Rejection on this search subset is not rejection on the domain.
      progress s!"Finished: structured witness search: {status candidate}"
  return none

/-- Call Blaster in-process on propositions constructed from decoded programs.
    Results are consumed as an inductive type, without parsing diagnostic text. -/
def solve (env : Environment) (c : Config) (oldProgram newProgram : PlutusCore.UPLC.Term.Program)
    (checkedResults : Option (IO.Ref (Array (Option Blaster.Smt.Result))) := none)
    (diagnostics : Option (IO.Ref (Array (String × Json))) := none)
    (observer : Solver.Observer := {})
    (dispatchInfo : Option (IO.Ref Json) := none) : IO (Array Blaster.Smt.Result × Option (List String)) := do
  let progress := observer.message
  let programs := #[toExpr oldProgram, toExpr newProgram]
  let plan := queries c
  let names := plan.map Query.name
  let skipRemaining := fun (checked : Nat) (reason : String) => do
    for pending in plan.toList.drop checked do
      progress s!"Skipping: {pending.name} ({reason})"
  let action : MetaM (Array Blaster.Smt.Result × Option (List String)) := do
    let (dispatchResults, oldAcceptanceModel) ← if c.splitDispatch && c.mode == "validator" then
        do
          let discovery := Dispatch.discover c.toLimits oldProgram newProgram c.dispatchCaseLimit
          if let some found ← searchDispatch c oldProgram newProgram programs discovery dispatchInfo diagnostics observer then
            pure (found.map some, none)
          else proveDispatch c oldProgram newProgram programs discovery dispatchInfo diagnostics observer
      else pure (#[], none)
    if plan.zipIdx.any (fun (query, index) => query.sides.size == 2 &&
        ((dispatchResults[index]?).getD none matches some (.Falsified _))) then
      if let some ref := checkedResults then ref.set dispatchResults
      return (dispatchResults.map (·.getD .Undetermined), oldAcceptanceModel)
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
        let witness := replayOldAcceptance c oldProgram newProgram []
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
      let primary ← match (dispatchResults[results.size]?).getD none with
        | some result =>
            progress s!"Using dispatch evidence [{query.name}]"
            pure result
        | none => do
            progress s!"Starting: {query.description} [{query.name}]"
            observer.reportPhase "preprocessing" (some query.name)
            let proposition ← queryProposition c query programs
            Solver.runQuery proposition query.name c.timeout query.wantsCounterexample
              diagnostics observer c.solverJobs c.solverSeed
      if let some ref := checkedResults then ref.modify (·.push (some primary))
      results := results.push primary
      progress s!"Finished: {query.name}: {status primary}"
      if c.mode == "validator" && query.sides.size == 2 then
        if let .Falsified model := primary then
          let witness := replayCounterexample c oldProgram newProgram model (query.sides[0]? == some 1)
          if replayConfirmed witness then
            skipRemaining results.size "regression confirmed by native replay"
            break
      if (query.name == "old_rejected" || query.name == "new_rejected") && (primary matches .Valid) then
        for (previous, i) in (plan.toList.take results.size).zipIdx do
          if let some evidence := queryEvidence c previous results then
            results := results.set! i .Valid
            if let some ref := checkedResults then ref.modify (fun rows => rows.set! i none)
            progress s!"Derived: {previous.name} (from {evidence})"
    -- Minting and withdrawal synthesis use the full rejection query. Spending can
    -- still try its distinct witness subsets after an unsuccessful query.
    if checksLedger c && comparisonsProved results && oldAcceptanceModel.isNone &&
        (c.spending || c.skipOldRejected) then
      let oldIndex := names.idxOf "old_rejected"
      let rejection := results[oldIndex]?.getD .Undetermined
      unless rejection matches .Valid do
        let bindings := match rejection with
          | .Falsified model => model
          | _ => []
        unless replayConfirmed (replayOldAcceptance c oldProgram newProgram bindings) do
          if let some model ← synthesizeOldAcceptance c oldProgram newProgram programs diagnostics observer then
            -- A replayed witness refutes universal rejection when that query was enabled.
            if oldIndex < results.size then
              results := results.set! oldIndex (.Falsified model)
            return (results, some model)
    return (results, oldAcceptanceModel)
  let (result, _) ← action.run' |>.toIO
    { fileName := "<uplc_equiv>", fileMap := default, maxRecDepth := 0, maxHeartbeats := 0 }
    { env }
  return result

def classifyFunction (c : Config) (results : Array Blaster.Smt.Result)
    (oldProgram newProgram : PlutusCore.UPLC.Term.Program) : Json := Id.run do
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
    ("input_domain", toJson (inputDomain c)),
    ("budget", c.budget.map (fun (cpu, memory) => Json.mkObj [("cpu", toJson cpu), ("memory", toJson memory)]) |>.getD Json.null)] ++ c.languageFields ++ c.stepLimitFields
  if oldProgram = newProgram then
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
    let witness := replayCounterexample c oldProgram newProgram model
    if replayConfirmed witness then
      return report inequivalent (if c.bounded then if c.equivalence then "The functions have different bounded observations on a replayed input." else "NEW fails to preserve an OLD constant result within the supplied limits on a replayed input." else "The functions produce different outcomes or returned values on a replayed input.")
        (details ++ [("counterexample", witness)])
    return report "inconclusive" "Function equivalence is unestablished: a limit, unsupported return value, or unreplayed countermodel prevented comparison."
      (details ++ [("diagnostic_counterexample", witness)])
  | .Undetermined => return report "inconclusive" "Function equivalence is unestablished: symbolic reasoning did not finish." details

def classify (c : Config) (results : Array Blaster.Smt.Result)
    (oldProgram newProgram : PlutusCore.UPLC.Term.Program)
    (domainWitness : Option PlutusCore.Data.Data := none)
    (oldAcceptanceModel : Option (List String) := none) : Json := Id.run do
  if c.mode == "function" then return classifyFunction c results oldProgram newProgram
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
          ("proof_domain", toJson (if c.minting then "ledger-valid structured minting transactions"
            else if c.withdrawal then "ledger-valid structured reward-withdrawal transactions"
            else if c.mixedLanguages then "ledger-valid shared V2/V3 spending transactions"
            else "ledger-valid structured spending contexts")),
          ("domain_witness", PlutusCore.Data.toDetailedJson raw), ("ledger_validity", auditLedgerContext c raw)]
      | _ => return domainIssue "unestablished" "Could not construct a ledger-valid context witnessing the selected domain; no preservation claim is made."
  let preserved := result "acceptance_preserved"
  let reversePreserved := result "reverse_acceptance_preserved"
  let candidates := [(false, result "no_acceptance_regression"), (false, preserved)] ++
    (if c.equivalence then [(true, result "reverse_no_acceptance_regression"), (true, reversePreserved)]
     else [])
  let mut regression : Option Json := none
  let mut diagnostic : Option Json := none
  for (reverse, candidate) in candidates do
    if let .Falsified model := candidate then
      let witness := replayCounterexample c oldProgram newProgram model reverse
      if replayConfirmed witness then
        regression := some witness
        break
      if diagnostic.isNone then diagnostic := some witness
  let complete := (preserved matches .Valid) && (!c.equivalence || (reversePreserved matches .Valid))
  let boundedPrefix := if c.bounded then "bounded_" else ""
  let successVerdict := boundedPrefix ++ if c.equivalence then "equivalent" else "preserved"
  let failureVerdict := boundedPrefix ++ if c.equivalence then "inequivalent" else "regression"
  let scope := if c.bounded then "within the supplied step and optional execution-budget limits" else "under the supplied budget"
  let (initialVerdict, initialExplanation) :=
    if regression.isSome then
      if c.equivalence then (failureVerdict, s!"One script accepts an input not accepted by the other {scope}.")
      else (failureVerdict, s!"An input accepted by OLD is not accepted by NEW {scope}.")
    else if diagnostic.isSome then
      ("inconclusive", "The symbolic countermodel could not be replayed as a ledger-valid acceptance regression.")
    else if complete then
      if c.equivalence then (successVerdict, s!"Both scripts accept the same inputs in the declared domain {scope}.")
      else (successVerdict, s!"NEW accepts every input accepted by OLD in the declared domain {scope}.")
    else ("inconclusive", "Acceptance preservation is unestablished: analysis or symbolic reasoning did not finish.")
  let mut verdict := initialVerdict
  let mut explanation := initialExplanation
  let mut acceptanceFields := []
  let (cpu, memory) := c.budget.getD (0, 0)
  if complete && regression.isNone && diagnostic.isNone then
    match result "old_rejected" with
    | .Valid =>
      verdict := "vacuously_" ++ successVerdict
      explanation := s!"OLD accepts no input in the declared domain {scope}; preservation is vacuous."
      let variant : PlutusCore.Default.BuiltinSemanticsVariant := if c.isV3 0 then
        .defaultFunSemanticsVariantE else .defaultFunSemanticsVariantD
      let costs := PlutusCore.UPLC.CekMachine.semVarToCosts variant
      let startup := costs.startupCost
      let budget : PlutusCore.UPLC.ExBudget.ExBudget := ⟨⟨cpu⟩, ⟨memory⟩⟩
      let belowStartup := c.budget.isSome && !budget.canAfford startup
      -- Every supported domain supplies at least one argument, hence its initial
      -- term is an application, independent of the script and input values.
      let belowFirstStep := c.budget.isSome && !budget.canAfford (startup + costs.stepCostApply)
      if belowStartup then
        explanation := "The supplied budget cannot cover OLD startup. Preservation is vacuous."
      else if belowFirstStep then
        explanation := "The supplied budget covers OLD startup but cannot cover its first application step. Preservation is vacuous."
      acceptanceFields := [("old_acceptance_status", toJson "rejected_everywhere"),
        ("vacuity_reason", toJson (if belowStartup then "startup_budget_exhausted"
          else if belowFirstStep then "initial_step_budget_exhausted"
          else if c.bounded then "old_rejects_bounded_domain" else "old_rejects_domain"))]
    | rejectionResult =>
      let model := match rejectionResult with
        | .Falsified model => model
        | _ => oldAcceptanceModel.getD []
      let witness := replayOldAcceptance c oldProgram newProgram model
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
    ("purpose", toJson c.purpose),
    ("check", toJson (if c.equivalence then "acceptance preservation in both directions" else "old acceptance implies new acceptance")),
    ("budget", c.budget.map (fun (cpu, memory) => Json.mkObj [("cpu", toJson cpu), ("memory", toJson memory)]) |>.getD Json.null)] ++
    c.languageFields ++ c.stepLimitFields ++
    [("context_limits", Json.mkObj [
      ("inputs_min", toJson (0 : Nat)), ("inputs_max", toJson c.maxInputs),
      ("outputs_min", toJson (0 : Nat)), ("outputs_max", toJson c.maxOutputs),
      ("signers_max", toJson c.maxSigners),
      ("earlier_spending_redeemers_max", toJson c.maxEarlierSpendingRedeemers), ("integer_bits", Json.null),
      ("inspected_byte_string_bytes", Json.null),
      ("value_policy_entries", toJson (2 : Nat)), ("tokens_per_policy", toJson (1 : Nat)),
      ("script_purpose", toJson (if c.minting then "minting" else if c.withdrawal then "withdrawal" else "spending")),
      ("validity_range", toJson "arbitrary Data")])] ++
    (if c.budget.isSome then
      let costModel := fun side => if c.isV3 side then "bundled post-Conway E" else "bundled post-Conway D"
      [("cost_model", toJson (if c.mixedLanguages then s!"OLD {costModel 0}, NEW {costModel 1}" else costModel 0))]
     else [("execution", toJson "uncosted")])
  let counterexample := match regression with
    | some witness => [("counterexample", witness)]
    | none => diagnostic.toList.map fun witness => ("diagnostic_counterexample", witness)
  let derivations := (queries c).toList.filterMap fun query =>
    (queryEvidence c query results).map fun evidence => (query.name, toJson evidence)
  let provenance := if derivations.isEmpty then [] else [("derived_queries", Json.mkObj derivations)]
  return report verdict explanation ([("input_domain", toJson (inputDomain c))] ++ details ++ ledgerFields ++ acceptanceFields ++ [
    ("queries", Json.mkObj (names.toList.zip (results.toList.map (toJson ∘ status)))),
    ("verification", toJson "Blaster SMT result; no reconstructed Lean proof term")] ++ provenance ++ counterexample)

/-- The bundled D/E cost models target Van Rossem (protocol version 11).
    Both V2 and V3 support UPLC 1.0.0 and 1.1.0 in that era. -/
private def validateProgramVersion (side language : String) :
    PlutusCore.UPLC.Term.Program → Except String Unit
  | .Program (.Version 1 0 0) _ | .Program (.Version 1 1 0) _ => .ok ()
  | .Program (.Version major minor patch) _ =>
    .error s!"{side} uses UPLC {major}.{minor}.{patch}, which is unsupported for {language} at protocol version 11. Expected UPLC 1.0.0 or 1.1.0."

/-- Check two decoded programs. Observers are optional; library checks are silent
    by default. inspectQueries can export or inspect the initial and checked plan. -/
def check (c : Config) (oldProgram newProgram : PlutusCore.UPLC.Term.Program)
    (observer : Solver.Observer := {})
    (inspectQueries : Environment → Array (Option Blaster.Smt.Result) → IO Unit := fun _ _ => pure ()) : IO Json := do
  IO.ofExcept c.validate
  if c.versionedArguments then
    IO.ofExcept (validateProgramVersion "OLD" (c.languageFor 0) oldProgram)
    IO.ofExcept (validateProgramVersion "NEW" (c.languageFor 1) newProgram)
  let progress := observer.message
  observer.reportPhase "preprocessing"
  if c.mode == "function" && decide (oldProgram = newProgram) then
    progress "Finished: program_identity: identical decoded UPLC programs"
    return classifyFunction c #[] oldProgram newProgram
  observer.reportPhase "validation"
  if checksLedger c then progress "Starting: constructing a ledger-model-valid domain witness"
  let domainWitness := if checksLedger c then nativeDomainWitness c else none
  if checksLedger c && domainWitness.isNone then
    return report "inconclusive" "Could not construct a ledger-valid context witnessing the selected domain; no preservation claim is made."
      ([("domain_status", toJson "unestablished"), ("input_domain", toJson (inputDomain c))] ++
        c.languageFields)
  if checksLedger c then progress "Finished: ledger-model-valid domain witness constructed"
  -- Resolve dependencies when the checker is used outside Lake or the repository.
  progress "Starting: preparing symbolic checker"
  observer.reportPhase "preprocessing"
  initSearchPath toolchainRoot (moduleSearchPath.map FilePath.mk)
  let env ← importModules #[{ module := `Equivalence.Queries }, { module := `Equivalence.ValidContext },
    { module := `Equivalence.Dispatch.Partition }, { module := `Blaster }] {} (loadExts := true)
  inspectQueries env #[]
  let checkedResults ← IO.mkRef #[]
  let diagnostics ← IO.mkRef #[]
  if c.skipOldRejected then progress "Skipping: old_rejected (--skip-old-rejected)"
  let dispatchInfo ← IO.mkRef Json.null
  let (results, oldAcceptanceModel) ←
    solve env c oldProgram newProgram (some checkedResults) (some diagnostics) observer (some dispatchInfo)
  inspectQueries env (← checkedResults.get)
  progress "Starting: validating replay witnesses and classifying results"
  observer.reportPhase "validation"
  let result := classify c results oldProgram newProgram domainWitness oldAcceptanceModel
  let dispatch ← dispatchInfo.get
  let result := if c.splitDispatch then result.setObjVal! "dispatch" dispatch else result
  let nativeProbe := ((dispatch.getObjVal? "winning_case").toOption.bind fun winner =>
    (winner.getObjValAs? Bool "native_probe").toOption).getD false
  let result := if nativeProbe then result.setObjVal! "verification"
    (toJson "Native replay of an automatically discovered dispatch case; no reconstructed Lean proof term") else result
  let diagnostics ← diagnostics.get
  return if diagnostics.isEmpty then result else
    result.setObjVal! "query_diagnostics" (Json.mkObj diagnostics.toList)

end Equivalence.Checker
