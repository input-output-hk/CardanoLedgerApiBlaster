import Equivalence.Portfolio

/-!
Runs Blaster preprocessing, SMT translation and Z3 solving as separate phases.
Exposes optional progress observers and records timeout or unknown-result diagnostics.
Manages solver cleanup and returns SMT results without reconstructing Lean proofs.
-/

open Lean

namespace Equivalence.Solver

abbrev Process := IO.Process.Child ⟨.piped, .piped, .piped⟩

/-- The active stage of a check and, when applicable, its query. -/
structure Phase where
  phase : String := "startup"
  query : Option String := none
  deriving ToJson, FromJson

/-- Optional diagnostics for embedding applications. -/
structure Observer where
  message : String → IO Unit := fun _ => pure ()
  phase : Phase → IO Unit := fun _ => pure ()

def Observer.reportPhase (observer : Observer) (phase : String)
    (query : Option String := none) : IO Unit :=
  observer.phase { phase := phase, query := query }

def describe (state : Phase) : String :=
  let label := match state.phase with
    | "loading" => "loading scripts"
    | "preprocessing" => "preprocessing"
    | "translation" => "translating/submitting the SMT query"
    | "z3" => "Z3 solving"
    | "validation" => "validating results and replaying witnesses"
    | "exporting" => "exporting Lean queries"
    | _ => "initializing the checker"
  label ++ (state.query.map (fun name => s!" [{name}]")).getD ""

private def unknownReason (reply : String) : String :=
  let reply := reply.trim
  let marker := "(:reason-unknown \""
  if reply.startsWith marker && reply.endsWith "\")" then
    (reply.drop marker.length).take (reply.length - marker.length - 2)
  else reply

/-- Run Blaster's optimizer and SMT translation separately so phase reporting
    does not depend on parsing Blaster's verbose diagnostic text. -/
def runQuery (proposition : Expr) (query : String) (timeout : Nat) (generateCex : Bool)
    (diagnostics : Option (IO.Ref (Array (String × Json))) := none)
    (observer : Observer := {}) (jobs : Nat := 1) (seed : Option Nat := none)
    (activeProcess : Option (IO.Ref (Option Process)) := none) : MetaM Blaster.Smt.Result := do
  let env := { (default : Blaster.Optimize.TranslateEnv) with
    optEnv.options.solverOptions.timeout := some timeout
    optEnv.options.solverOptions.randomSeed := if jobs == 1 then seed else none
    optEnv.options.solverOptions.onlyOptimize := true
    optEnv.options.solverOptions.reconstructProofs := false
    optEnv.options.solverOptions.generateCex := generateCex }
  let action : Blaster.Optimize.TranslateEnvT Blaster.Smt.Result := do
    observer.reportPhase "preprocessing" (some query)
    -- Reuse Blaster's proposition validation, axiom handling and optimization.
    let (optimizedResult, optimized) ← Blaster.Smt.Translate.main proposition (logUndetermined := false)
    if !(optimizedResult matches .Undetermined) then
      observer.reportPhase "validation" (some query)
      return optimizedResult
    modify fun env => { env with
      optEnv.options.solverOptions.onlyOptimize := false
      optEnv.options.solverOptions.onlySmtLib := jobs > 1
      optEnv.options.solverOptions.dumpSmtLib := jobs > 1 }
    observer.reportPhase "translation" (some query)
    let result ← try
      Blaster.Smt.setBlasterProcess
      if let some ref := activeProcess then ref.set (← get).smtEnv.smtProc
      let term ← Blaster.Smt.translateExpr optimized
      Blaster.Smt.assertTerm (Blaster.Smt.notSmt term)
      observer.reportPhase "z3" (some query)
      let outcome ← if jobs > 1 then
        Portfolio.solve (← get) jobs timeout seed
      else do
        let result ← Blaster.Smt.checkSat
        let reason ← if result matches .Undetermined then do
          let some process := (← get).smtEnv.smtProc | pure ""
          -- Ask before closing the process: unknown is not necessarily timeout.
          process.stdin.putStrLn "(get-info :reason-unknown)"
          process.stdin.flush
          Blaster.Smt.getOutputEval process.stdout
        else pure ""
        pure { result, seed, reason : Portfolio.Outcome }
      let result := outcome.result
      let reason := unknownReason outcome.reason
      let timedOut := reason == "timeout"
      if jobs > 1 || (result matches .Undetermined) then
        let status := match result with
          | .Valid => "valid"
          | .Falsified _ => "falsified"
          | .Undetermined => if timedOut then "timeout" else "unknown"
        let fields := [
          ("phase", toJson "z3"), ("status", toJson status),
          ("reason", toJson reason), ("limit_seconds", toJson timeout)] ++
          if jobs > 1 then [("workers", toJson jobs), ("winner_seed", toJson outcome.seed)] else []
        if let some ref := diagnostics then ref.modify (·.push (query, Json.mkObj fields))
        observer.message (if jobs > 1 then
          match result with
          | .Undetermined => s!"Z3 portfolio returned unknown [{query}]: {reason}"
          | _ => s!"Z3 portfolio finished [{query}] with seed {outcome.seed.map toString |>.getD "default"}"
        else if timedOut then s!"Z3 timed out after {timeout}s [{query}]"
        else s!"Z3 returned unknown [{query}]: {reason}")
      pure result
    catch error =>
      -- Cleanup must not replace the original setup/solver error with a broken pipe.
      try discard Blaster.Smt.exitSmt catch _ => pure ()
      -- Retain the handle for the timed caller's finalizer if cleanup failed.
      throw error
    discard Blaster.Smt.exitSmt
    if let some ref := activeProcess then ref.set none
    observer.reportPhase "validation" (some query)
    return result
  let (result, _) ← action.run env
  return result

/-- A fresh Meta/Core state confines cancellation to one speculative case.
The ordinary checker retains its outer process watchdog as a hard deadline. -/
def runQueryTimed (environment : Environment) (proposition : Expr) (query : String)
    (timeout wall : Nat) (diagnostics : Option (IO.Ref (Array (String × Json))))
    (observer : Observer) (jobs : Nat) (seed : Option Nat) : IO (Option Blaster.Smt.Result) := do
  let token ← IO.CancelToken.new
  let done ← IO.mkRef false
  let active ← IO.mkRef (none : Option Process)
  let phase ← IO.mkRef ({} : Phase)
  let deadline := (← IO.monoMsNow) + wall * 1000
  let timer ← IO.asTask (prio := .dedicated) do
    repeat
      if ← done.get then break
      if (← IO.monoMsNow) ≥ deadline then
        token.set
        -- A blocked solver read does not poll Lean's cancellation token.
        if let some process ← active.get then
          try process.kill catch _ => pure ()
        break
      IO.sleep 25
  let observer := { observer with phase := fun state => do
    phase.set state
    observer.phase state }
  try
    let action := runQuery proposition query (min timeout wall) true diagnostics observer jobs seed (some active)
    let (result, _) ← action.run' |>.toIO
      { fileName := "<uplc_equiv dispatch>", fileMap := default,
        maxRecDepth := 0, maxHeartbeats := 0, cancelTk? := some token } { env := environment }
    return some result
  catch error =>
    unless ← token.isSet do throw error
    let state ← phase.get
    observer.message s!"Dispatch case stopped after {wall}s during {describe state}"
    if let some ref := diagnostics then ref.modify (·.push (query, Json.mkObj [
      ("phase", toJson state.phase), ("status", toJson "case_timeout"),
      ("reason", toJson "dispatch case deadline"), ("limit_seconds", toJson wall)]))
    return none
  finally
    done.set true
    discard (IO.ofExcept timer.get)
    -- Interrupts can bypass MetaM's ordinary exception handlers.
    if let some process ← active.get then
      try
        if (← process.tryWait).isNone then process.kill
        discard process.wait
      catch _ => pure ()

end Equivalence.Solver
