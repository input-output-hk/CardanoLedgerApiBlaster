import Blaster

/-!
Runs Blaster preprocessing, SMT translation and Z3 solving as separate phases.
Exposes optional progress observers and records timeout or unknown-result diagnostics.
Manages solver cleanup and returns SMT results without reconstructing Lean proofs.
-/

open Lean

namespace Equivalence.Solver

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
    (observer : Observer := {}) : MetaM Blaster.Smt.Result := do
  let env := { (default : Blaster.Optimize.TranslateEnv) with
    optEnv.options.solverOptions.timeout := some timeout
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
    modify fun env => { env with optEnv.options.solverOptions.onlyOptimize := false }
    observer.reportPhase "translation" (some query)
    let result ← try
      Blaster.Smt.setBlasterProcess
      let term ← Blaster.Smt.translateExpr optimized
      Blaster.Smt.assertTerm (Blaster.Smt.notSmt term)
      observer.reportPhase "z3" (some query)
      let result ← Blaster.Smt.checkSat
      if result matches .Undetermined then
        let some process := (← get).smtEnv.smtProc
          | return result
        -- Ask before closing the process: unknown is not necessarily timeout.
        process.stdin.putStrLn "(get-info :reason-unknown)"
        process.stdin.flush
        let reason := unknownReason (← Blaster.Smt.getOutputEval process.stdout)
        let timedOut := reason == "timeout"
        let diagnostic := Json.mkObj [
          ("phase", toJson "z3"), ("status", toJson (if timedOut then "timeout" else "unknown")),
          ("reason", toJson reason), ("limit_seconds", toJson timeout)]
        if let some ref := diagnostics then ref.modify (·.push (query, diagnostic))
        observer.message (if timedOut then
          s!"Z3 timed out after {timeout}s [{query}]"
          else s!"Z3 returned unknown [{query}]: {reason}")
      pure result
    catch error =>
      -- Cleanup must not replace the original setup/solver error with a broken pipe.
      try discard Blaster.Smt.exitSmt catch _ => pure ()
      throw error
    discard Blaster.Smt.exitSmt
    observer.reportPhase "validation" (some query)
    return result
  let (result, _) ← action.run env
  return result

end Equivalence.Solver
