import Equivalence.Cli

namespace Tests.Equivalence.Support

open Lean System

def config : _root_.Equivalence.Cli.Config := { equivalence := true, inputs := "integer", budget := some (10000000000, 14000000), timeout := 5 }

/-- Shared budgeted settings for random CAPE explorations. -/
def acceptanceConfig : _root_.Equivalence.Cli.Config :=
  { config with equivalence := false }

def check (report : Json) (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError s!"{message}\n{report.pretty}"

def field (report : Json) (path : List String) : IO Json := do
  match path.foldlM Json.getObjVal? report with
  | .ok value => return value
  | .error message => throw <| IO.userError s!"{path}: {message}\n{report.pretty}"

/-- Follow the constructor-field path used by a context-inspecting script. -/
def dataField (value : Json) (path : List Nat) : IO Json :=
  path.foldlM (fun value index => do
    let fields ← IO.ofExcept ((← field value ["fields"]).getArr?)
    let some value := fields[index]?
      | throw <| IO.userError s!"Missing Data field {index}: {value.pretty}"
    return value) value

def expect [ToJson α] (report : Json) (path : List String) (expected : α) : IO Unit := do
  let actual ← field report path
  check report (actual == toJson expected) s!"Expected {path} = {toJson expected}, got {actual}"

def verdict (report : Json) (expected : String) : IO Unit :=
  expect report ["verdict"] expected

def noCounterexample (report : Json) : IO Unit :=
  check report (report.getObjVal? "counterexample").toOption.isNone "Unexpected counterexample"

def witness (report : Json) : IO Json := do
  let result ← field report ["counterexample"]
  expect result ["replayed"] true
  return result

def withProgram (term : String) (action : FilePath → IO α) : IO α :=
  IO.FS.withTempDir fun directory => do
    let path := directory / "script with \"quotes\".uplc"
    IO.FS.writeFile path s!"(program 1.1.0 {term})"
    action path

def progress (message : String) : IO Unit := do
  let stderr ← IO.getStderr
  stderr.putStrLn message
  stderr.flush

/-- The Tests library builds the native CLI first. Each comparison gets a fresh
    process, an 8 GiB Lean memory limit and a wall-clock deadline. -/
def runBounded (c : _root_.Equivalence.Cli.Config) : IO Json := do
  let child ← IO.Process.spawn {
    cmd := ".lake/build/bin/uplc_equiv"
    args := #["--worker", "--json", "--language", c.language, "--inputs", c.inputs,
      "--format-left", c.leftFormat.getD c.format,
      "--format-right", c.rightFormat.getD c.format,
      "--variation", c.variation,
      "--timeout", toString c.timeout] ++
      (if c.equivalence then #["--equivalence"] else #[]) ++
      (c.budget.toArray.flatMap fun (cpu, memory) => #["--budget", toString cpu, toString memory]) ++
      (c.caseIndex.toArray.flatMap fun index => #["--case", toString index]) ++ c.scripts
    env := #[("UPLC_EQUIV_TEST_WORKER", some "1")]
    setsid := true
    stdin := .null
    stdout := .piped
    stderr := .piped }
  let output ← IO.asTask child.stdout.readToEnd
  let errors ← IO.asTask child.stderr.readToEnd
  let finished ← _root_.Equivalence.Cli.waitUntil child ((← IO.monoMsNow) + 60000)
  let stdout ← IO.ofExcept output.get
  let stderr ← IO.ofExcept errors.get
  unless finished do
    return _root_.Equivalence.Cli.report "inconclusive"
      "Script check reached its 60-second wall-clock limit, including preprocessing."
      [("input_domain", toJson (_root_.Equivalence.Cli.inputDomain c))]
  match Json.parse stdout with
  | .ok report => return report
  | .error error => throw <| IO.userError s!"Checker worker failed: {error}\n{stdout}\n{stderr}"

/-- Keep synthetic regressions isolated too: repeated in-process SMT runs retain
    substantial compiler state in the test module's elaboration process. -/
def comparePrograms (left right : String) (c : _root_.Equivalence.Cli.Config := config) : IO Json :=
  withProgram left fun l => withProgram right fun r =>
    runBounded { c with scripts := #[l.toString, r.toString], format := "textual" }

/-- Select distinct decoded programs with the same ordering and seed handling
for every CLI exploration. Legacy seed names remain fallback aliases. -/
def randomPaths (label : String) (directory : FilePath) (legacySeed : String)
    (limits : String) : IO (Array String) := do
  let seed ← match (← IO.getEnv "SEED") <|> (← IO.getEnv legacySeed) with
    | some value => match value.toNat? with
      | some seed => pure seed
      | none => throw <| IO.userError s!"SEED (or {legacySeed}) must be a nonnegative integer"
    | none => pure (← IO.getRandomBytes 8).toUInt64LE!.toNat
  IO.setRandSeed seed
  let entries ← System.FilePath.readDir directory
  let paths := (entries.filterMap fun entry =>
    if entry.path.extension == some "cbor_hex" then some entry.path.toString else none).qsort (· < ·)
  unless paths.size ≥ 2 do throw <| IO.userError s!"{label} requires at least two scripts"
  let left ← IO.rand 0 (paths.size - 1)
  let program ← _root_.Equivalence.Cli.readProgram paths[left]! "single_cbor_hex"
  let representation := reprStr program
  let mut candidates := #[]
  for path in paths do
    let other ← _root_.Equivalence.Cli.readProgram path "single_cbor_hex"
    if representation != reprStr other then candidates := candidates.push path
  if candidates.isEmpty then throw <| IO.userError s!"{label} requires two distinct programs"
  let right := candidates[← IO.rand 0 (candidates.size - 1)]!
  progress s!"SEED={seed}: {paths[left]!} vs {right} ({limits})"
  return #[paths[left]!, right]

structure Exploration where
  label : String
  directory : FilePath
  legacySeed : String
  config : _root_.Equivalence.Cli.Config
  modes : Array String
  variationGroups : Array (Array _root_.Equivalence.Context.Variation)
  caseCount : Nat
  caseForMode : String → Nat → Nat := fun _ index => index

def selectFamily (c : _root_.Equivalence.Cli.Config) (mode : String)
    (caseIndex : Nat) (variation : String) : _root_.Equivalence.Cli.Config :=
  { c with inputs := mode, caseIndex := some caseIndex, variation := variation }

/-- One runner owns sampling, deadlines, verdicts, replay requirements and domain
checks. Only fixture data and the finite case mapping vary between contracts. -/
def runExploration (scenario : Exploration) : IO Unit := do
  let (cpu, memory) := scenario.config.budget.getD (0, 0)
  let limits := s!"shared budget: CPU {cpu}, memory {memory}"
  let paths ← randomPaths scenario.label scenario.directory scenario.legacySeed limits
  let mut inconclusive : Array String := #[]
  for (group, round) in scenario.variationGroups.toList.zipIdx do
    let sampledCase ← IO.rand 0 (scenario.caseCount - 1)
    let some selected := group[← IO.rand 0 (group.size - 1)]?
      | throw <| IO.userError "Empty variation group"
    let variation := selected.name
    for mode in scenario.modes do
      let caseIndex := scenario.caseForMode mode sampledCase
      progress s!"{scenario.label} round {round + 1}/{scenario.variationGroups.size}: {mode}, case {caseIndex}, variation {variation} (60s wall-clock limit)"
      let report ← runBounded (selectFamily { scenario.config with scripts := paths } mode caseIndex variation)
      progress s!"{mode}: {report.pretty}"
      let result ← IO.ofExcept ((← field report ["verdict"]).getStr?)
      match result with
      | "preserved" =>
        expect report ["queries", "acceptance_preserved"] "valid"
        noCounterexample report
      | "regression" => discard <| witness report
      | "equivalent" =>
        for query in ["acceptance_preserved", "reverse_acceptance_preserved"] do
          expect report ["queries", query] "valid"
        noCounterexample report
      | "inequivalent" => discard <| witness report
      | "inconclusive" =>
        inconclusive := inconclusive.push s!"{mode}, case {caseIndex}, variation {variation}"
      | _ => check report false "Unexpected checker verdict"
      let domain ← IO.ofExcept ((← field report ["input_domain"]).getStr?)
      for restriction in [s!"restricted to case {caseIndex}:", "no ledger-validity restriction"] do
        check report ((domain.splitOn restriction).length != 1) s!"Missing domain restriction: {restriction}"
      if variation != "baseline" then
        check report ((domain.splitOn s!"context variation: {variation}:").length != 1)
          "Missing context variation description"
  unless inconclusive.isEmpty do
    throw <| IO.userError s!"Inconclusive {scenario.label} checks:\n{String.intercalate "\n" inconclusive.toList}"

def checkCaseSelection (label : String) (c : _root_.Equivalence.Cli.Config) (script : String)
    (cases : Array (String × Nat × Nat)) : IO Unit := do
  progress s!"{label}: checking case selection (60s wall-clock limit per check)"
  withProgram "(lam c (con unit ()))" fun accept => do
    for (mode, unsignedCase, signedCase) in cases do
      let selected := { c with scripts := #[script, accept.toString], rightFormat := some "textual" }
      progress s!"{label} case selection: {mode}, unsigned case {unsignedCase}"
      let absent ← runBounded (selectFamily selected mode unsignedCase "baseline")
      verdict absent "inequivalent"
      let w ← witness absent
      expect w ["old", "accepts"] false
      expect w ["new", "accepts"] true
      progress s!"{label} case selection: {mode}, signed case {signedCase}"
      let present ← runBounded (selectFamily selected mode signedCase "baseline")
      verdict present "equivalent"
      noCounterexample present

/-- UPLC expression selecting a path through Data constructor fields. -/
def dataFieldTerm (term : String) (indices : List Nat) : String :=
  indices.foldl (fun term index =>
    let fields := s!"[(force (force (builtin sndPair))) [(builtin unConstrData) {term}]]"
    let rest := (List.range index).foldl (fun list _ => s!"[(force (builtin tailList)) {list}]") fields
    s!"[(force (builtin headList)) {rest}]") term

def contextFieldTerm (indices : List Nat) : String := dataFieldTerm "c" indices

/-- A context predicate that errors when the condition holds and returns unit otherwise. -/
def rejectIf (condition : String) : String :=
  "(lam c (force [[[(force (builtin ifThenElse)) " ++
    condition ++ "] (delay (error))] (delay (con unit ()))]))"

def rejectDataAt (path : List Nat) (expected : String) : String :=
  rejectIf s!"[[(builtin equalsData) {contextFieldTerm path}] (con data ({expected}))]"

end Tests.Equivalence.Support
