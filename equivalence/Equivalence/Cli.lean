import Equivalence.Checker
import Equivalence.Pretty
import Equivalence.AssuranceExport

/-!
Exposes the equivalence checker as a command-line tool for script files.
Parses options, loads programs, exports Lean queries and formats result reports.
Supervises an isolated worker to enforce a wall-clock limit and report live progress.
-/

open Lean System
open PlutusCore.UPLC.ScriptEncoding.Internal

namespace Equivalence.Cli

open Checker

structure Config extends Checker.Config where
  inputsSpecified : Bool := false
  maximaSpecified : Bool := false
  formatSpecified : Bool := false
  scripts : Array String := #[]
  format : String := "single_cbor_hex"
  leftFormat : Option String := none
  rightFormat : Option String := none
  leftValidator : Option String := none
  rightValidator : Option String := none
  wallTimeout : Nat := 180
  emitLean : Option String := none
  emitAssurance : Option String := none
  json : Bool := false
  worker : Bool := false


instance : Coe Config Checker.Config := ⟨Config.toConfig⟩

/-- Progress is separate from the final report, including in JSON mode. -/
def progress (message : String) : IO Unit := do
  let stderr ← IO.getStderr
  stderr.putStrLn message
  stderr.flush

def usage : String := "Usage: lake exe uplc_equiv OLD NEW [options]

Validator mode checks that NEW accepts every input accepted by OLD within the supplied limits.
Function mode compares returned constants and success/error outcomes, ignoring execution costs.
  --mode validator|function                             Default validator; function defaults to integer inputs, no budget
  --steps N                                             Execution step limit; analysis guard unless --bounded (default 100000)
  --bounded                                             Compare observations within step/budget limits; OLD results/acceptance preserved
Budgeted checks use the bundled post-Conway cost model (V3: E; V1/V2: D).
  --inputs valid-context                                Validator default: structured V3 spending contexts, ledger-constrained queries and checked replays
  --max-inputs N                                        Include 0..N transaction inputs (validator only; default 2)
  --max-outputs N                                       Include 0..N transaction outputs (validator only; default 2)
  --max-signers N                                       Include 0..N signer keys (validator only; default 2)
  --redeemer DATA                                       Fix the spending redeemer (textual Plutus Data)
  --datum DATA                                          Fix the spending datum (textual Plutus Data); other context fields remain symbolic
  DATA shorthand: integers become I n; text becomes UTF-8 bytes; JSON quotes force text.
  --inputs integer|data|data3                            Function input domain (default integer)
  --format FORMAT                                       textual, flat, flat_hex, single_cbor_hex (default), double_cbor_hex, blueprint
                                                        Auto: .uplc is textual; .json (including plutus.json) is blueprint
  --format-left FORMAT                                  Override the left script format
  --format-right FORMAT                                 Override the right script format
  --validator-left ID_OR_TITLE                          Select a validator in the OLD blueprint
  --validator-right ID_OR_TITLE                         Select a validator in the NEW blueprint
  --language VERSION                                    PlutusV3 (default); function mode also supports PlutusV1/PlutusV2
  --budget CPU MEMORY                                   Shared execution-unit limits (required for strict validators; optional with --bounded or function mode)
  --equivalence                                         Check both directions (validators or --bounded functions)
  --dispatch-timeout SECONDS                            Deadline per case query, including preprocessing (default 10); implies --split-dispatch
  --dispatch-cases N                                    Maximum discovered cases, plus a catch-all (default 16); implies --split-dispatch
  --split-dispatch                                      Prove datum/redeemer cases plus their catch-all; fall back on incomplete proofs
  --skip-old-rejected                                   Skip the deferred OLD rejection query; OLD acceptance still needs a witness
  -jN, -j N                                             Race N Z3 workers per query (default 1)
  --seed S                                              Starting seed; workers use S through S+N-1 (default 0)
  --timeout SECONDS                                     Shared Z3 deadline per query (default 20)
  --wall-timeout SECONDS                                Limit the complete check, including preprocessing (default 180)
  --emit-lean FILE                                      Save the checked Lean queries for inspection
  --emit-assurance DIR                                  Write assurance.json and comparison.json to a new directory (NEW must be a blueprint)
  --json                                                Emit a JSON report
  --help                                                Show this help

Strict function comparisons require observable outcomes. Bounded functions observe absent constants as none.
Bounded validators count step exhaustion as nonacceptance and still require an OLD-accepting witness.
Exit codes: 0 preserved/equivalent/bounded_preserved/bounded_equivalent (validator: OLD acceptance witnessed),
1 regression/inequivalent/bounded_regression/bounded_inequivalent,
2 inconclusive, 3 tool/usage error, 4 vacuous validator preservation/equivalence (including bounded).
Validator budget exhaustion is rejection; strict function budget exhaustion is inconclusive.
Analysis exhaustion is inconclusive; --bounded instead declares steps part of the comparison scope.
Validator V3 acceptance requires a unit result; V1/V2 accept any successful result.
Budgets are per-script allocations; cost coefficients are bundled, not network parameters.
Counterexamples include the input and both outcomes, replayed with the same limits.
Progress is printed live on stderr; the final text or JSON report is printed on stdout.
Verification uses Blaster's SMT results without reconstructed Lean proof terms.\n"

def formats : List String := ["textual", "flat", "flat_hex", "single_cbor_hex", "double_cbor_hex", "blueprint"]

/-- Structured phase events are an internal worker-to-supervisor protocol. -/
def phasePrefix : String := "[uplc_equiv:phase] "

def reportPhase (phase : String) (query : Option String := none) : IO Unit := do
  let stderr ← IO.getStderr
  stderr.putStrLn (phasePrefix ++ (toJson ({ phase := phase, query := query } : Solver.Phase)).compress)
  stderr.flush

def phaseEvent? (line : String) : Option Solver.Phase := do
  guard (line.startsWith phasePrefix)
  let json ← (Json.parse (line.drop phasePrefix.length)).toOption
  (fromJson? json).toOption

def observer : Solver.Observer where
  message := progress
  phase := fun state => reportPhase state.phase state.query

def natOption (key value : String) (positive := false) : Except String Nat := do
  let some n := value.toNat? | throw s!"{key} expects a nonnegative integer"
  if positive && n == 0 then throw s!"{key} must be positive"
  return n

/-- Integers and text are shorthand; JSON strings force text, and Data constructors stay explicit. -/
def parseData (option source : String) : Except String PlutusCore.Data.Data := do
  let original := source
  let source := source.trim
  if let some value := source.toInt? then return .I value
  if source.startsWith "\"" then
    let json ← (Json.parse source).mapError (fun error => s!"{option}: {error}")
    let .str text := json | throw s!"{option} expects a JSON string"
    return .B (PlutusCore.String.encodeUtf8 text)
  if source.startsWith "--" then throw s!"{option} expects a value before {source}"
  let keyword := String.mk (source.data.takeWhile (fun c => !c.isWhitespace))
  if !["I", "B", "Constr", "List", "Map"].contains keyword && !source.startsWith "(" then
    return .B (PlutusCore.String.encodeUtf8 original)
  let program ← PlutusCore.UPLC.TextEncoding.programFromString
    (s!"(program 1.1.0 (con data ({source})))")
      |>.mapError (fun error => s!"{option}: {error}")
  let .Program _ (.Const (.Data datum)) := program
    | throw s!"{option} expects textual Plutus Data"
  return datum

private def inferFormat (path : String) : Option String :=
  if path.endsWith ".uplc" then some "textual"
  else if path.endsWith ".json" then some "blueprint"
  else none

def parse (c : Config) : List String → Except String Config
  | [] => do
    unless c.scripts.size == 2 do throw "expected old and new script paths"
    let c := if c.mode == "function" && !c.inputsSpecified && c.inputs == "valid-context" then
      { c with inputs := "integer" } else c
    let c := if c.formatSpecified then c else
      { c with
        leftFormat := c.leftFormat.orElse fun _ => inferFormat c.scripts[0]!
        rightFormat := c.rightFormat.orElse fun _ => inferFormat c.scripts[1]! }
    if c.mode == "function" && c.maximaSpecified then
      throw "--max-inputs, --max-outputs and --max-signers are validator options"
    c.toConfig.validate
    for f in [c.format, c.leftFormat.getD c.format, c.rightFormat.getD c.format] do
      unless formats.contains f do throw s!"unsupported format: {f}"
    if c.leftValidator.isSome && c.leftFormat.getD c.format != "blueprint" then
      throw "--validator-left requires a blueprint OLD input"
    if c.rightValidator.isSome && c.rightFormat.getD c.format != "blueprint" then
      throw "--validator-right requires a blueprint NEW input"
    if c.emitAssurance.isSome && c.rightFormat.getD c.format != "blueprint" then
      throw "--emit-assurance requires a blueprint NEW input"
    return c
  | "--bounded" :: rest => parse { c with bounded := true } rest
  | "--mode" :: v :: rest => parse { c with mode := v } rest
  | "--steps" :: v :: rest => do parse { c with steps := ← natOption "--steps" v true } rest
  | "--equivalence" :: rest => parse { c with equivalence := true } rest
  | "--budget" :: cpu :: memory :: rest => do
    parse { c with budget := some (← natOption "--budget CPU" cpu, ← natOption "--budget MEMORY" memory) } rest
  | "--json" :: rest => parse { c with json := true } rest
  | "--worker" :: rest => parse { c with worker := true, json := true } rest
  | "--dispatch-timeout" :: v :: rest => do
    parse { c with splitDispatch := true, dispatchTimeout := ← natOption "--dispatch-timeout" v true } rest
  | "--dispatch-cases" :: v :: rest => do
    parse { c with splitDispatch := true, dispatchCaseLimit := ← natOption "--dispatch-cases" v true } rest
  | "--split-dispatch" :: rest => parse { c with splitDispatch := true } rest
  | "--skip-old-rejected" :: rest => parse { c with skipOldRejected := true } rest
  | "--format" :: v :: rest => parse { c with format := v, formatSpecified := true } rest
  | "--format-left" :: v :: rest => parse { c with leftFormat := some v } rest
  | "--format-right" :: v :: rest => parse { c with rightFormat := some v } rest
  | "--validator-left" :: v :: rest => parse { c with leftValidator := some v } rest
  | "--validator-right" :: v :: rest => parse { c with rightValidator := some v } rest
  | "--language" :: v :: rest => parse { c with language := v } rest
  | "--redeemer" :: v :: rest => do
    parse { c with redeemer := some (← parseData "--redeemer" v) } rest
  | "--datum" :: v :: rest => do
    parse { c with datum := some (← parseData "--datum" v) } rest
  | "--inputs" :: v :: rest => parse { c with inputs := v, inputsSpecified := true } rest
  | "--input" :: v :: rest => parse { c with inputs := v, inputsSpecified := true } rest
  | "--max-inputs" :: v :: rest => do
    parse { c with maxInputs := ← natOption "--max-inputs" v, maximaSpecified := true } rest
  | "--max-outputs" :: v :: rest => do
    parse { c with maxOutputs := ← natOption "--max-outputs" v, maximaSpecified := true } rest
  | "--max-signers" :: v :: rest => do
    parse { c with maxSigners := ← natOption "--max-signers" v, maximaSpecified := true } rest
  | "--emit-assurance" :: v :: rest => parse { c with emitAssurance := some v } rest
  | "--emit-lean" :: v :: rest => parse { c with emitLean := some v } rest
  | "--seed" :: v :: rest => do parse { c with solverSeed := some (← natOption "--seed" v) } rest
  | "-j" :: v :: rest => do parse { c with solverJobs := ← natOption "-j" v true } rest
  | "--timeout" :: v :: rest => do parse { c with timeout := ← natOption "--timeout" v true } rest
  | "--wall-timeout" :: v :: rest => do parse { c with wallTimeout := ← natOption "--wall-timeout" v true } rest
  | v :: rest =>
    if v.startsWith "-j" && v != "-j" then do
      parse { c with solverJobs := ← natOption "-j" (v.drop 2) true } rest
    else if v.startsWith "-" then .error s!"unknown or incomplete option: {v}"
    else parse { c with scripts := c.scripts.push v } rest

private def blueprintScript (source : String) (selector language : Option String)
    (requireReference : Bool) :
    Except String AssuranceExport.BlueprintScript := do
  let blueprint ← PlutusCore.UPLC.BlueprintEncoding.Internal.parseBlueprint source
  let version := blueprint.preamble.plutusVersion
  if let some language := language then
    unless version == language.replace "PlutusV" "v" do
      throw s!"blueprint declares '{version}', but the comparison uses {language}; select the matching --language"
  let validator ← match selector with
    | some name => PlutusCore.UPLC.BlueprintEncoding.Internal.resolveValidator blueprint.validators name
    | none =>
      match (blueprint.validators.filter (·.compiledCode.isSome)).toList with
      | [validator] => pure validator
      | [] => throw "no validator with compiledCode in the blueprint"
      | validators =>
        let choices := String.intercalate ", " (validators.map fun v => v.id.getD v.title)
        throw s!"multiple validators with compiledCode; use --validator-left or --validator-right ({choices})"
  let some code := validator.compiledCode | throw s!"validator '{validator.title}' has no compiledCode"
  let code := code.trim
  let hash ← PlutusCore.UPLC.BlueprintEncoding.Internal.actualScriptHash version code
  if let some expected := validator.hash then
    unless expected.toLower == hash do
      throw s!"validator '{validator.title}': compiledCode hash mismatch (declared {expected}, computed {hash})"
  let reference := selector.getD (validator.id.getD validator.title)
  if requireReference && selector.isNone then
    unless (PlutusCore.UPLC.BlueprintEncoding.Internal.resolveValidator blueprint.validators reference).toOption.any
        (fun v => v.id == validator.id && v.title == validator.title && v.compiledCode == validator.compiledCode) do
      throw "assurance export needs an unambiguous validator reference; use --validator-left or --validator-right"
  return { code, hash, reference }

private def readInput (path : FilePath) (format : String) (selector language : Option String)
    (requireReference := false) :
    IO (PlutusCore.UPLC.Term.Program × AssuranceExport.Input) := do
  let bytes ← IO.FS.readBinFile path
  let input : AssuranceExport.Input := { path, format, bytes }
  let parsed : Except String (PlutusCore.UPLC.Term.Program × AssuranceExport.Input) := do
    if format == "flat" then
      let program ← flatEncodedScriptFromBytestring?
        (String.mk (bytes.data.toList.map (fun b => Char.ofNat b.toNat)))
      return (program, input)
    let some source := String.fromUTF8? bytes | throw "expected UTF-8 input"
    if format == "blueprint" then
      let script ← blueprintScript source selector language requireReference
      let program ← singleCborEncodedScriptFromHex? script.code
      return (program, { input with blueprint := some script })
    let program ← match format with
      | "textual" => PlutusCore.UPLC.TextEncoding.programFromString source
      | "flat_hex" => flatEncodedScriptFromHex? source.trim
      | "single_cbor_hex" => singleCborEncodedScriptFromHex? source.trim
      | "double_cbor_hex" => doubleCborEncodedScriptFromHex? source.trim
      | _ => throw s!"unsupported format: {format}"
    return (program, input)
  IO.ofExcept (parsed.mapError fun error => s!"Cannot import {path}: {error}")

def readProgram (path format : String) : IO PlutusCore.UPLC.Term.Program := do
  return (← readInput path format none none).1

private def sourceHeader (c : Config) (leftCode rightCode : Option String) : IO String := do
  let scriptDecl (name path format : String) (code : Option String) : IO String := do
    if let some hex := code then
      return s!"abbrev {name} : PlutusCore.UPLC.PlutusScript.PlutusScript := " ++
        s!"⟨.{c.language}, singleCborEncodedScriptFromHexM {toJson hex |>.compress}⟩\n"
    let path ← IO.FS.realPath path
    return s!"#import_uplc {name} {c.language} {format} {toJson path.toString |>.compress}\n"
  let left ← scriptDecl "left" c.scripts[0]! (c.leftFormat.getD c.format) leftCode
  let right ← scriptDecl "right" c.scripts[1]! (c.rightFormat.getD c.format) rightCode
  return "import Equivalence.Queries\nimport Equivalence.ValidContext\nimport Blaster\nopen Equivalence.Queries\n" ++
    left ++ right

/-- An identity check needs neither recursive evaluation nor an SMT solver.
    Export a kernel-checkable proof of the same function query. -/
private def emitIdenticalSource (c : Config) (header : String) : IO Unit := do
  let some file := c.emitLean | return
  let some query := (queries c)[0]?
    | throw <| IO.userError "No function query to export"
  let (cpu, memory) := c.budget.getD (0, 0)
  let binders := if c.inputs == "data3" then "datum redeemer context" else "input"
  IO.FS.writeFile file (header ++
    s!"\n-- Identical decoded programs establish equivalence without evaluating them.\nexample : {query.declaration} left.script right.script {cpu} {memory} {c.language == "PlutusV3"} {c.budget.isSome} {c.steps} := by\n  intro {binders}\n  exact Or.inl rfl\n")

private def emitSource (env : Environment) (c : Config) (header : String)
    (checkedResults : Array (Option Blaster.Smt.Result) := #[])
    (diagnostics : Json := .null) : IO Unit := do
  let some file := c.emitLean | return
  -- A subset countermodel falsifies the original property, but the original
  -- unspecialized solver need not reproduce that result within the same timeout.
  let checkedResults := if c.splitDispatch then #[] else checkedResults
  let header := header ++ if c.splitDispatch then
    "\n-- Dispatch uses an exhaustive partition, including its catch-all. This export\n-- contains the original full-domain queries without per-result annotations.\n-- Per-case results and partition proofs are reported in the JSON dispatch field.\n" else ""
  let chunks ← (queries c).toList.zipIdx.filterMapM fun (query, i) => do
    -- Skip queries derived logically or short-circuited by a native witness.
    let expected := if checkedResults.isEmpty then some "" else do
      let some result ← checkedResults[i]? | none
      -- A single solver need not repeat an inconclusive portfolio search.
      if c.solverJobs > 1 && (result matches .Undetermined) then
        some ""
      else
        let code := match result with
          | .Valid => 0
          | .Falsified _ => 1
          | .Undetermined => 2
        some s!" (solve-result: {code})"
    let some expected := expected | return none
    let action : MetaM Format := do
      let scriptType := mkConst ``PlutusCore.UPLC.PlutusScript.PlutusScript
      Meta.withLocalDeclD `left scriptType fun left =>
        Meta.withLocalDeclD `right scriptType fun right => do
          let field := mkConst ``PlutusCore.UPLC.PlutusScript.PlutusScript.script
          let programs := #[mkApp field left, mkApp field right]
          let expression ← if c.mode == "validator" then queryPredicate c query programs
            else queryProposition c query programs
          PrettyPrinter.ppExpr expression
    let (rendered, _) ← action.run' |>.toIO
      { fileName := "<uplc_equiv>", fileMap := default, maxRecDepth := 0, maxHeartbeats := 0 } { env }
    let renderData := fun value => do
      let action : MetaM Format := PrettyPrinter.ppExpr (toExpr value)
      let (rendered, _) ← action.run' |>.toIO
        { fileName := "<uplc_equiv>", fileMap := default } { env }
      pure rendered.pretty
    let datumText ← c.datum.mapM renderData
    let redeemerText ← c.redeemer.mapM renderData
    let counts := s!"{c.maxInputs} {c.maxOutputs} {c.maxSigners}"
    let proposition := match datumText, redeemerText with
      | some datum, some redeemer =>
        s!"valid_context_fixed% {counts} ({datum}) ({redeemer}) ({rendered.pretty})"
      | some datum, none => s!"valid_context_datum% {counts} ({datum}) ({rendered.pretty})"
      | none, some redeemer => s!"valid_context_redeemer% {counts} ({redeemer}) ({rendered.pretty})"
      | none, none => if c.mode == "validator" then
          s!"valid_context% {counts} ({rendered.pretty})" else rendered.pretty
    let seed := if c.solverJobs > 1 && !checkedResults.isEmpty then
      ((diagnostics.getObjVal? query.name).toOption.map fun entry =>
        (entry.getObjValAs? Nat "winner_seed").toOption).getD c.solverSeed
      else c.solverSeed
    let seed := seed.map (fun seed => s!" (random-seed: {seed})") |>.getD ""
    return some s!"\n-- {query.name}\n#blaster (timeout: {c.timeout}){seed}{expected} (reconstruct-proofs: 0) (gen-cex: {if query.wantsCounterexample then 1 else 0}) [{proposition}]\n"
  let scope := if checksLedger c then
    "\n-- These queries require Ledger.validArguments for each structured context.\n-- The checker separately checks a native ledger-model-valid domain witness\n-- and validates counterexample replays; those checks are not reproduced here.\n"
    else ""
  IO.FS.writeFile file (header ++
    (if c.mode == "function" then "\n-- Function countermodels are separately replayed by the checker.\n" else
      "\n-- The checker separately replays an OLD-accepting input before reporting\n-- nonvacuous preservation. These queries alone do not reproduce that replay.\n") ++
    scope ++ String.join chunks)

private def assuranceSettings (c : Config) : Json :=
  Json.mkObj (c.toConfig.stepLimitFields ++ [
    ("mode", toJson c.mode), ("language", toJson c.language), ("inputs", toJson c.inputs),
    ("equivalence", toJson c.equivalence),
    ("budget", c.budget.map (fun (cpu, memory) =>
      Json.mkObj [("cpu", toJson cpu), ("memory", toJson memory)]) |>.getD Json.null),
    ("max_inputs", toJson c.maxInputs), ("max_outputs", toJson c.maxOutputs),
    ("max_signers", toJson c.maxSigners), ("timeout", toJson c.timeout),
    ("wall_timeout", toJson c.wallTimeout), ("skip_old_rejected", toJson c.skipOldRejected),
    ("split_dispatch", toJson c.splitDispatch), ("dispatch_cases", toJson c.dispatchCaseLimit),
    ("dispatch_timeout", toJson c.dispatchTimeout)])

private def assuranceClaim (c : Config) : String :=
  let relation := if c.mode == "validator" then
    if c.equivalence then "NEW and OLD accept the same inputs"
    else "NEW accepts every input accepted by OLD"
  else if !c.bounded then "NEW and OLD have equal function outcomes"
  else if c.equivalence then "NEW and OLD observe the same function results"
  else "NEW preserves every function result observed from OLD"
  relation ++ " in the input domain and limits recorded in the comparison artifact."

def run (c : Config) : IO Json := do
  let c ← IO.ofExcept (parse c [])
  if let some dir := c.emitAssurance then
    if ← (FilePath.mk dir).pathExists then
      throw (IO.userError s!"Assurance output directory already exists: {dir}")
  let inputPath (path : String) : IO FilePath :=
    if c.emitAssurance.isSome then IO.FS.realPath path else pure path
  progress "Starting: loading OLD script"
  reportPhase "loading"
  let (left, oldInput) ← readInput (← inputPath c.scripts[0]!) (c.leftFormat.getD c.format)
    c.leftValidator (some c.language) c.emitAssurance.isSome
  progress "Starting: loading NEW script"
  let (right, newInput) ← readInput (← inputPath c.scripts[1]!) (c.rightFormat.getD c.format)
    c.rightValidator (some c.language) c.emitAssurance.isSome
  let header ← if c.emitLean.isSome then
    sourceHeader c (oldInput.blueprint.map (·.code)) (newInput.blueprint.map (·.code))
    else pure ""
  let checkedExport ← IO.mkRef (none : Option (Environment × Array (Option Blaster.Smt.Result)))
  let inspectQueries := fun env results => do
    if c.emitLean.isSome then
      if results.isEmpty then
        progress "Starting: exporting initial Lean queries"
        reportPhase "exporting"
        emitSource env c header
      else
        checkedExport.set (some (env, results))
  let result ← Checker.check c.toConfig left right observer inspectQueries
  if let some (env, results) ← checkedExport.get then
    progress "Starting: exporting checked Lean queries"
    reportPhase "exporting"
    emitSource env c header results ((result.getObjVal? "query_diagnostics").toOption.getD .null)
  if c.emitLean.isSome && c.mode == "function" && decide (left = right) then
    progress "Starting: exporting program-identity proof"
    reportPhase "exporting"
    emitIdenticalSource c header
  if let some dir := c.emitAssurance then
    if (result.getObjValAs? String "verdict").toOption != some "error" then
      progress "Starting: exporting assurance evidence"
      reportPhase "exporting"
      AssuranceExport.write dir oldInput newInput (assuranceClaim c) (assuranceSettings c) result
  return result

partial def waitUntil (child : IO.Process.Child cfg) (deadline : Nat) : IO Bool := do
  if (← child.tryWait).isSome then return true
  if (← IO.monoMsNow) ≥ deadline then
    child.kill
    discard child.wait
    return false
  IO.sleep 50
  waitUntil child deadline

/-- Forward worker diagnostics immediately, retaining them for malformed reports. -/
def forwardDiagnostics (source : IO.FS.Handle) (phase : IO.Ref Solver.Phase)
    (started : Nat) : IO String := do
  let target ← IO.getStderr
  let mut captured := ""
  repeat
    let line ← source.getLine
    if line.isEmpty then break
    let line ← match phaseEvent? line with
      | some current => do
        let previous ← phase.get
        phase.set current
        pure (if previous.phase == current.phase && previous.query == current.query then ""
          else s!"Phase: {Solver.describe current}\n")
      | none => pure line
    if line.isEmpty then continue
    let elapsed := (← IO.monoMsNow) - started
    let fraction := toString (elapsed % 1000)
    let padding := String.mk (List.replicate (3 - fraction.length) '0')
    let line := s!"[{elapsed / 1000}.{padding}{fraction}s] {line}"
    target.putStr line
    target.flush
    captured := captured ++ line
  return captured

/-- A second instance of this native executable isolates the checker so the parent
    can stop preprocessing and its Z3 children at the wall-clock deadline. -/
def supervise (args : List String) (c : Config) : IO Json := do
  let started ← IO.monoMsNow
  let child ← IO.Process.spawn {
    cmd := (← IO.appPath).toString
    args := ("--worker" :: args).toArray
    setsid := true
    stdin := .null
    stdout := .piped
    stderr := .piped }
  let phase ← IO.mkRef ({} : Solver.Phase)
  let output ← IO.asTask child.stdout.readToEnd
  let errors ← IO.asTask (forwardDiagnostics child.stderr phase started)
  let finished ← waitUntil child (started + c.wallTimeout * 1000)
  let stdout ← IO.ofExcept output.get
  let stderr ← IO.ofExcept errors.get
  unless finished do
    let phase ← phase.get
    return report "inconclusive" s!"Wall-clock limit of {c.wallTimeout}s reached during {Solver.describe phase}."
      [("timeout", Json.mkObj [("kind", toJson "wall_clock"), ("limit_seconds", toJson c.wallTimeout),
        ("phase", toJson phase.phase), ("query", toJson phase.query)])]
  match Json.parse stdout with
  | .ok value => return value
  | .error error => return report "error" s!"Checker worker failed: {error}\n{stdout}\n{stderr}"

def exitCode (r : Json) : UInt32 :=
  match (r.getObjValAs? String "verdict").toOption with
  | some "preserved" | some "equivalent" | some "bounded_equivalent" | some "bounded_preserved" => 0
  | some "regression" | some "inequivalent" | some "bounded_inequivalent" | some "bounded_regression" => 1
  | some "inconclusive" => 2
  | some "vacuously_preserved" | some "vacuously_equivalent"
  | some "vacuously_bounded_preserved" | some "vacuously_bounded_equivalent" => 4
  | _ => 3

def printReport (json : Bool) (r : Json) : IO Unit := do
  if json then IO.println r.pretty
  else
    IO.println s!"{(r.getObjValAs? String "verdict").toOption.getD "error"}: {(r.getObjValAs? String "explanation").toOption.getD ""}"
    if let .ok domain := r.getObjValAs? String "input_domain" then
      IO.println s!"Input domain: {domain}"
    if let .ok steps := r.getObjValAs? Nat "steps" then
      if (r.getObjValAs? String "step_limit_kind").toOption == some "execution_bound" then
        IO.println s!"Execution step bound: {steps}"
      else
        IO.println s!"Analysis step guard: {steps} (exhaustion is inconclusive)"
    if let .ok budget := r.getObjVal? "budget" then
      if budget != Json.null then IO.println s!"Budget: {budget.compress}"
    if let .ok execution := r.getObjValAs? String "execution" then
      IO.println s!"Execution: {execution}"
    if let .ok model := r.getObjValAs? String "cost_model" then
      IO.println s!"Cost model: {model}"
    if let .ok queries := r.getObjVal? "queries" then
      for name in #["program_identity", "function_equivalent", "bounded_function_preserved", "bounded_function_equivalent", "no_acceptance_regression", "acceptance_preserved", "reverse_no_acceptance_regression", "reverse_acceptance_preserved"] do
        if let .ok value := queries.getObjValAs? String name then IO.println s!"  {name}: {value}"
      if let .ok verification := r.getObjValAs? String "verification" then IO.println verification
    if let .ok diagnostics := r.getObjVal? "query_diagnostics" then
      if let .ok entries := diagnostics.getObj? then
        for (name, diagnostic) in entries.toList do
          let reason := (diagnostic.getObjValAs? String "reason").toOption.getD "unknown"
          match (diagnostic.getObjValAs? String "status").toOption with
          | some "case_timeout" =>
            let limit := (diagnostic.getObjValAs? Nat "limit_seconds").toOption.getD 0
            let phase := (diagnostic.getObjValAs? String "phase").toOption.getD "unknown"
            IO.println s!"  {name}: dispatch case stopped after {limit}s during {phase}"
          | some "timeout" =>
            let limit := (diagnostic.getObjValAs? Nat "limit_seconds").toOption.getD 0
            IO.println s!"  {name}: Z3 timed out after {limit}s"
          | some "valid" | some "falsified" =>
            let seed := (diagnostic.getObjValAs? Nat "winner_seed").toOption.map toString |>.getD "default"
            IO.println s!"  {name}: Z3 portfolio finished with seed {seed}"
          | _ => IO.println s!"  {name}: Z3 returned unknown ({reason})"
    if let .ok dispatch := r.getObjVal? "dispatch" then
      if let .ok cases := dispatch.getObjValAs? (Array Json) "cases" then
        if (dispatch.getObjValAs? Bool "exhaustive").toOption == some true then
          IO.println s!"Dispatch partition: {cases.size} cases checked (including the catch-all when reached)"
        else IO.println s!"Dispatch search: {cases.size} cases tried"
      if let .ok winner := dispatch.getObjVal? "winning_case" then
        if winner != Json.null then
          let datum := (winner.getObjValAs? String "datum").toOption.getD "?"
          let redeemer := (winner.getObjValAs? String "redeemer").toOption.getD "?"
          IO.println s!"  Winning case: datum={datum}; redeemer={redeemer}"
          if let .ok exclusions := winner.getObjValAs? (List String) "exclusions" then
            for condition in exclusions do IO.println s!"    {condition}"
    if let .ok witness := r.getObjVal? "counterexample" then
      IO.println <| Pretty.counterexample ((r.getObjValAs? String "mode").toOption == some "validator") witness
    if (r.getObjVal? "old_acceptance_witness").isOk then
      IO.println "OLD acceptance: confirmed by native replay (input available with --json)"

end Equivalence.Cli

open Equivalence.Cli

def main (args : List String) : IO UInt32 := do
  if args.contains "--help" || args.contains "-h" then
    IO.println usage
    return 0
  else
    let parsed := parse {} args
    let config := parsed.toOption.getD { json := args.contains "--json" }
    let result ← try
      match parsed with
      | .error error => pure (Equivalence.Checker.report "error" error)
      | .ok c => if c.worker then run c else supervise args c
    catch error => pure (Equivalence.Checker.report "error" error.toString)
    printReport config.json result
    return exitCode result
