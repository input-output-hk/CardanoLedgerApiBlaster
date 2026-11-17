import Blaster

/-! A bounded portfolio over one already translated SMT query. Each worker owns
its Z3 process and model; only the seed differs. No Lean optimization is repeated. -/

open Lean
open Blaster.Optimize

namespace Equivalence.Portfolio

structure Outcome where
  result : Blaster.Smt.Result
  seed : Option Nat := none
  worker : Nat := 0
  reason : String := ""

private def runWorker (env : TranslateEnv) (seed : Option Nat) : MetaM Outcome := do
  let action : TranslateEnvT Outcome := do
    for command in env.smtEnv.smtCommands do
      Blaster.Smt.trySubmitCommand! command (!(command matches .setSimplifier _))
      -- Set the seed as soon as acknowledgements are enabled, before any
      -- declarations or assertions can initialize solver search state.
      if command matches .setOption ":print-success" "true" then
        Blaster.Smt.setRandomSeed seed
    -- This worker already has a dedicated thread. Read directly rather than
    -- queuing Blaster's additional reader task on Lean's bounded task pool.
    Blaster.Smt.submitCommand .checkSat
    let some process := (← get).smtEnv.smtProc
      | throwError "portfolio worker has no solver process"
    let reply := (← process.stdout.getLine).replace "\r" ""
    let result : Blaster.Smt.Result ← match reply with
      | "sat\n" => pure (.Falsified [])
      | "unsat\n" => pure .Valid
      | "unknown\n" => pure .Undetermined
      | error => throwError "Unexpected SMT result: {error}"
    let reason ← if result matches .Undetermined then do
      process.stdin.putStrLn "(get-info :reason-unknown)"
      process.stdin.flush
      pure ((← process.stdout.getLine).replace "\r" "")
    else pure ""
    return { result, seed, reason := reason.trim }
  return (← action.run env).1

private def stop (processes : Array (IO.Process.Child ⟨.piped, .piped, .piped⟩)) : IO Unit := do
  for process in processes do
    try process.kill catch _ => pure ()
  for process in processes do
    try discard process.wait catch _ => pure ()

/-- Race independent SMT searches under a single deadline. An unknown result
    does not cancel other workers. Models are read from the winning worker. -/
def solve (env : TranslateEnv) (jobs timeout : Nat) (startSeed : Option Nat := none) : MetaM Outcome := do
  let coreContext ← readThe Core.Context
  let coreState ← getThe Core.State
  let metaContext ← readThe Meta.Context
  let metaState ← getThe Meta.State
  -- References keep newly acquired resources visible to the finalizer even
  -- when the body throws; exception handlers snapshot ordinary mutable locals.
  let processes ← IO.mkRef (#[] : Array (IO.Process.Child ⟨.piped, .piped, .piped⟩))
  let tasks ← IO.mkRef (#[] : Array (Task (Except IO.Error Outcome)))
  let deadline := (← IO.monoMsNow) + timeout * 1000
  try
    for i in [:jobs] do
      let process ← Blaster.Smt.createBlasterProcess
      processes.modify (·.push process)
      let workerEnv := { env with
        smtEnv.smtProc := some process
        optEnv.options.solverOptions.dumpSmtLib := false }
      let seed := match startSeed with
        | some base => some (base + i)
        | none => if i == 0 then none else some i
      let task ← IO.asTask (do
        let (outcome, _, _) ← (runWorker workerEnv seed).toIO coreContext coreState metaContext metaState
        return { outcome with worker := i }) Task.Priority.dedicated
      tasks.modify (·.push task)
    let mut pending ← tasks.get
    let mut reasons : Array String := #[]
    let mut winner : Option Outcome := none
    while !pending.isEmpty && winner.isNone do
      if let some token := coreContext.cancelTk? then
        if ← token.isSet then throwInterruptException
      let mut unfinished := #[]
      for task in pending do
        if ← IO.hasFinished task then
          let outcome ← IO.ofExcept task.get
          if outcome.result matches .Undetermined then
            reasons := reasons.push outcome.reason
          else if winner.isNone then
            winner := some outcome
        else unfinished := unfinished.push task
      pending := unfinished
      if winner.isSome || pending.isEmpty then break
      if (← IO.monoMsNow) ≥ deadline then break
      IO.sleep 5
    if let some outcome := winner then
      let index := outcome.worker
      let workers ← processes.get
      let some process := workers[index]?
        | throwError "portfolio winner has no solver process"
      stop (workers.zipIdx.filterMap fun (p, i) => if i == index then none else some p)
      processes.set #[process]
      -- Only the selected solver reads a model. Killing a loser while Blaster
      -- is parsing its model could leave a reader waiting for truncated output.
      let result ← if outcome.result matches .Falsified _ then do
        let modelEnv := { env with smtEnv.smtProc := some process }
        let (model, _) ← Blaster.Smt.getModel.run modelEnv
        pure (.Falsified model)
      else pure outcome.result
      return { outcome with result }
    let timedOut := !pending.isEmpty || reasons.all (· == "(:reason-unknown \"timeout\")")
    return {
      result := .Undetermined
      reason := if timedOut then "(:reason-unknown \"timeout\")" else
        reasons[0]?.getD "(:reason-unknown \"unknown\")" }
  finally
    stop (← processes.get)
    for task in (← tasks.get) do discard (IO.wait task)

end Equivalence.Portfolio
