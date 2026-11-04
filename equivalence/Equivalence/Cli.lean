import Equivalence.Checker

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
  wallTimeout : Nat := 180
  emitLean : Option String := none
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
  --inputs valid-context                                Validator default: structured V3 spending contexts, ledger-checked witnesses/replays
  --max-inputs N                                        Include 0..N structured inputs (validator only; default 2)
  --max-outputs N                                       Include 0..N structured outputs (validator only; default 2)
  --max-signers N                                       Include 0..N signer keys (validator only; default 2)
  --inputs integer|data|data3                            Function input domain (default integer)
  --format FORMAT                                       textual, flat, flat_hex, single_cbor_hex (default), double_cbor_hex; .uplc paths default to textual
  --format-left FORMAT                                  Override the left script format
  --format-right FORMAT                                 Override the right script format
  --language VERSION                                    PlutusV3 (default); function mode also supports PlutusV1/PlutusV2
  --budget CPU MEMORY                                   Shared execution-unit limits (required for strict validators; optional with --bounded or function mode)
  --equivalence                                         Check both directions (validators or --bounded functions)
  --skip-old-rejected                                   Skip the deferred OLD rejection query; OLD acceptance still needs a witness
  --timeout SECONDS                                     Z3 timeout per query (default 20)
  --wall-timeout SECONDS                                Limit the complete check, including preprocessing (default 180)
  --emit-lean FILE                                      Save the checked Lean queries for inspection
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

def formats : List String := ["textual", "flat", "flat_hex", "single_cbor_hex", "double_cbor_hex"]

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

def parse (c : Config) : List String → Except String Config
  | [] => do
    unless c.scripts.size == 2 do throw "expected old and new script paths"
    let c := if c.mode == "function" && !c.inputsSpecified && c.inputs == "valid-context" then
      { c with inputs := "integer" } else c
    let c := if c.formatSpecified then c else
      { c with
        leftFormat := c.leftFormat.orElse fun _ => if c.scripts[0]!.endsWith ".uplc" then some "textual" else none
        rightFormat := c.rightFormat.orElse fun _ => if c.scripts[1]!.endsWith ".uplc" then some "textual" else none }
    if c.mode == "function" && c.maximaSpecified then
      throw "--max-inputs, --max-outputs and --max-signers are validator options"
    c.toConfig.validate
    for f in [c.format, c.leftFormat.getD c.format, c.rightFormat.getD c.format] do
      unless formats.contains f do throw s!"unsupported format: {f}"
    return c
  | "--bounded" :: rest => parse { c with bounded := true } rest
  | "--mode" :: v :: rest => parse { c with mode := v } rest
  | "--steps" :: v :: rest => do parse { c with steps := ← natOption "--steps" v true } rest
  | "--equivalence" :: rest => parse { c with equivalence := true } rest
  | "--budget" :: cpu :: memory :: rest => do
    parse { c with budget := some (← natOption "--budget CPU" cpu, ← natOption "--budget MEMORY" memory) } rest
  | "--json" :: rest => parse { c with json := true } rest
  | "--worker" :: rest => parse { c with worker := true, json := true } rest
  | "--skip-old-rejected" :: rest => parse { c with skipOldRejected := true } rest
  | "--format" :: v :: rest => parse { c with format := v, formatSpecified := true } rest
  | "--format-left" :: v :: rest => parse { c with leftFormat := some v } rest
  | "--format-right" :: v :: rest => parse { c with rightFormat := some v } rest
  | "--language" :: v :: rest => parse { c with language := v } rest
  | "--inputs" :: v :: rest => parse { c with inputs := v, inputsSpecified := true } rest
  | "--input" :: v :: rest => parse { c with inputs := v, inputsSpecified := true } rest
  | "--max-inputs" :: v :: rest => do
    parse { c with maxInputs := ← natOption "--max-inputs" v, maximaSpecified := true } rest
  | "--max-outputs" :: v :: rest => do
    parse { c with maxOutputs := ← natOption "--max-outputs" v, maximaSpecified := true } rest
  | "--max-signers" :: v :: rest => do
    parse { c with maxSigners := ← natOption "--max-signers" v, maximaSpecified := true } rest
  | "--emit-lean" :: v :: rest => parse { c with emitLean := some v } rest
  | "--timeout" :: v :: rest => do parse { c with timeout := ← natOption "--timeout" v true } rest
  | "--wall-timeout" :: v :: rest => do parse { c with wallTimeout := ← natOption "--wall-timeout" v true } rest
  | v :: rest =>
    if v.startsWith "-" then .error s!"unknown or incomplete option: {v}"
    else parse { c with scripts := c.scripts.push v } rest

def readProgram (path format : String) : IO PlutusCore.UPLC.Term.Program := do
  let parsed : Except String PlutusCore.UPLC.Term.Program ← match format with
    | "textual" => do pure <| PlutusCore.UPLC.TextEncoding.programFromString (← IO.FS.readFile path)
    | "flat" => do
      let bytes ← IO.FS.readBinFile path
      pure <| flatEncodedScriptFromBytestring? (String.mk (bytes.data.toList.map (fun b => Char.ofNat b.toNat)))
    | "flat_hex" => do pure <| flatEncodedScriptFromHex? (← IO.FS.readFile path).trim
    | "single_cbor_hex" => do pure <| singleCborEncodedScriptFromHex? (← IO.FS.readFile path).trim
    | "double_cbor_hex" => do pure <| doubleCborEncodedScriptFromHex? (← IO.FS.readFile path).trim
    | _ => throw <| IO.userError s!"unsupported format: {format}"
  match parsed with
  | .ok program => return program
  | .error error => throw <| IO.userError s!"Cannot import {path}: {error}"

def sourceHeader (c : Config) : IO String := do
  let left ← IO.FS.realPath c.scripts[0]!
  let right ← IO.FS.realPath c.scripts[1]!
  return s!"import Equivalence.Queries\nimport Equivalence.ValidContext\nimport Blaster\nopen Equivalence.Queries\n#import_uplc left {c.language} {c.leftFormat.getD c.format} {toJson left.toString |>.compress}\n#import_uplc right {c.language} {c.rightFormat.getD c.format} {toJson right.toString |>.compress}\n"

/-- An identity check needs neither recursive evaluation nor an SMT solver.
    Export a kernel-checkable proof of the same function query. -/
def emitIdenticalSource (c : Config) : IO Unit := do
  let some file := c.emitLean | return
  let header ← sourceHeader c
  let some query := (queries c)[0]?
    | throw <| IO.userError "No function query to export"
  let (cpu, memory) := c.budget.getD (0, 0)
  let binders := if c.inputs == "data3" then "datum redeemer context" else "input"
  IO.FS.writeFile file (header ++
    s!"\n-- Identical decoded programs establish equivalence without evaluating them.\nexample : {query.declaration} left.script right.script {cpu} {memory} {c.language == "PlutusV3"} {c.budget.isSome} {c.steps} := by\n  intro {binders}\n  exact Or.inl rfl\n")

def emitSource (env : Environment) (c : Config)
    (checkedResults : Array (Option Blaster.Smt.Result) := #[]) : IO Unit := do
  let some file := c.emitLean | return
  let header ← sourceHeader c
  let chunks ← (queries c).toList.zipIdx.filterMapM fun (query, i) => do
    -- Skip queries derived logically or short-circuited by a native witness.
    let expected := if checkedResults.isEmpty then some "" else do
      let some result ← checkedResults[i]? | none
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
    let proposition := if c.mode == "validator" then
      s!"valid_context% {c.maxInputs} {c.maxOutputs} {c.maxSigners} ({rendered.pretty})"
      else rendered.pretty
    return some s!"\n-- {query.name}\n#blaster (timeout: {c.timeout}){expected} (reconstruct-proofs: 0) (gen-cex: {if query.wantsCounterexample then 1 else 0}) [{proposition}]\n"
  let scope := if checksLedger c then
    "\n-- These queries prove preservation over the declared context shape's raw-Data superset.\n-- The checker separately checks a native ledger-model-valid domain witness\n-- and validates counterexample replays; those checks are not reproduced here.\n"
    else ""
  IO.FS.writeFile file (header ++
    (if c.mode == "function" then "\n-- Function countermodels are separately replayed by the checker.\n" else
      "\n-- The checker separately replays an OLD-accepting input before reporting\n-- nonvacuous preservation. These queries alone do not reproduce that replay.\n") ++
    scope ++ String.join chunks)

def run (c : Config) : IO Json := do
  let c ← IO.ofExcept (parse c [])
  progress "Starting: loading OLD script"
  reportPhase "loading"
  let left ← readProgram c.scripts[0]! (c.leftFormat.getD c.format)
  progress "Starting: loading NEW script"
  let right ← readProgram c.scripts[1]! (c.rightFormat.getD c.format)
  let inspectQueries := fun env results => do
    if c.emitLean.isSome then
      progress (if results.isEmpty then "Starting: exporting initial Lean queries"
        else "Starting: exporting checked Lean queries")
      reportPhase "exporting"
      emitSource env c results
  let result ← Checker.check c.toConfig left right observer inspectQueries
  if c.emitLean.isSome && c.mode == "function" && decide (left = right) then
    progress "Starting: exporting program-identity proof"
    reportPhase "exporting"
    emitIdenticalSource c
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
          if (diagnostic.getObjValAs? String "status").toOption == some "timeout" then
            let limit := (diagnostic.getObjValAs? Nat "limit_seconds").toOption.getD 0
            IO.println s!"  {name}: Z3 timed out after {limit}s"
          else IO.println s!"  {name}: Z3 returned unknown ({reason})"
    if let .ok witness := r.getObjVal? "counterexample" then
      IO.println s!"Counterexample:\n{witness.pretty}"
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
