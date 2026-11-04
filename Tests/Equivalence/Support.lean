import EquivalenceTest.Protocol

namespace Tests.Equivalence.Support

open Lean System EquivalenceTest
open PlutusCore.Data (Data)

/-- Transform a present datum while preserving the surrounding script-info encoding. -/
def mapSpendingDatum (change : Data → Data) (scriptInfo : Data) : Data :=
  match scriptInfo with
  | .Constr tag [reference, .Constr option [d]] =>
    .Constr tag [reference, .Constr option [change d]]
  | other => other

def modifyField (value : Data) (index : Nat) (change : Data → Data) : Data :=
  match value with
  | .Constr tag fields => .Constr tag (fields.modify index change)
  | other => other

/-- Test limits and fixture paths are independent of command-line options. -/
structure Config extends _root_.Equivalence.Checker.Config where
  scripts : Array String := #[]
  format : String := "single_cbor_hex"
  wallTimeout : Nat := 60

instance : Coe Config _root_.Equivalence.Checker.Config := ⟨Config.toConfig⟩

-- Validator tests use a small configured structured domain; dedicated limit
-- tests exercise larger maxima. Function tests select their own input domain.
def config : Config := { equivalence := true, maxInputs := 1, maxOutputs := 1, maxSigners := 1, budget := some (10000000000, 14000000), timeout := 5 }

/-- Shared settings for directional acceptance checks. -/
def acceptanceConfig : Config :=
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

def readProgram (path : String) (format : String := "single_cbor_hex") : IO PlutusCore.UPLC.Term.Program := do
  IO.ofExcept (Protocol.decode { source := ← IO.FS.readFile path, format := format })

private partial def waitUntil (child : IO.Process.Child cfg) (deadline : Nat) : IO Bool := do
  if (← child.tryWait).isSome then return true
  if (← IO.monoMsNow) ≥ deadline then
    child.kill
    discard child.wait
    return false
  IO.sleep 50
  waitUntil child deadline

/-- Each library check runs in a fresh native test worker, without CLI parsing,
    file loading, reporting or supervision code. -/
def runRequest (request : Protocol.Request) (wallTimeout : Nat) : IO Json := do
  let child ← IO.Process.spawn {
    cmd := ".lake/build/bin/equivalence_test_worker"
    setsid := true
    stdin := .piped
    stdout := .piped
    stderr := .piped }
  child.stdin.putStrLn (toJson request).compress
  child.stdin.flush
  let (_, child) ← child.takeStdin
  let output ← IO.asTask child.stdout.readToEnd
  let errors ← IO.asTask child.stderr.readToEnd
  let wallTimeout := min wallTimeout 60
  let finished ← waitUntil child ((← IO.monoMsNow) + wallTimeout * 1000)
  let stdout ← IO.ofExcept output.get
  let stderr ← IO.ofExcept errors.get
  unless finished do
    return _root_.Equivalence.Checker.report "inconclusive"
      s!"Library check reached its {wallTimeout}-second test deadline."
  match Json.parse stdout with
  | .ok report => return report
  | .error error => throw <| IO.userError s!"Library test worker failed: {error}\n{stdout}\n{stderr}"

/-- Compare checked-in fixtures using the library API. -/
def compareFixtures (c : Config) : IO Json := do
  unless c.scripts.size == 2 do throw <| IO.userError "Expected two test fixtures"
  runRequest {
    options := c.toConfig
    old := { source := ← IO.FS.readFile c.scripts[0]!, format := c.format }
    new := { source := ← IO.FS.readFile c.scripts[1]!, format := c.format } } c.wallTimeout

/-- Synthetic programs go straight to the library worker, without temporary files. -/
def comparePrograms (left right : String) (c : Config := config) : IO Json :=
  runRequest {
    options := c.toConfig
    old := { source := s!"(program 1.1.0 {left})", format := "textual" }
    new := { source := s!"(program 1.1.0 {right})", format := "textual" } } c.wallTimeout

/-- UPLC expression selecting a path through Data constructor fields. -/
def dataFieldTerm (term : String) (indices : List Nat) : String :=
  indices.foldl (fun term index =>
    let fields := s!"[(force (force (builtin sndPair))) [(builtin unConstrData) {term}]]"
    let rest := (List.range index).foldl (fun list _ => s!"[(force (builtin tailList)) {list}]") fields
    s!"[(force (builtin headList)) {rest}]") term

def contextFieldTerm (indices : List Nat) : String := dataFieldTerm "c" indices

def datumTerm : String := contextFieldTerm [2, 1, 0]

/-- A context predicate that errors when the condition holds and returns unit otherwise. -/
def rejectIf (condition : String) : String :=
  "(lam c (force [[[(force (builtin ifThenElse)) " ++
    condition ++ "] (delay (error))] (delay (con unit ()))]))"

def acceptIf (condition : String) : String :=
  "(lam c (force [[[(force (builtin ifThenElse)) " ++
    condition ++ "] (delay (con unit ()))] (delay (error))]))"

def rejectDataAt (path : List Nat) (expected : String) : String :=
  rejectIf s!"[[(builtin equalsData) {contextFieldTerm path}] (con data ({expected}))]"

end Tests.Equivalence.Support
