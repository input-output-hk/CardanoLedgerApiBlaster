import Equivalence.Queries
import Equivalence.Model
import Equivalence.HTLC
import Equivalence.Vesting
import Equivalence.Escrow
import Blaster

open Lean System
open PlutusCore.UPLC.ScriptEncoding.Internal

namespace Equivalence.Cli

/-- Use the toolchain this executable was built with, including outside the repo.
    This is evaluated at compile time, so checking invokes neither Lean nor Lake. -/
elab "toolchain_root%" : term => do
  return toExpr (← findSysroot).toString

def toolchainRoot : String := toolchain_root%

/-- Include path dependencies as well as Lake's git-package cache. -/
elab "module_search_path%" : term => do
  return toExpr ((← searchPathRef.get).map FilePath.toString)

def moduleSearchPath : List String := module_search_path%

-- Same runtime guard used by Lean's --memory option (private in Lean.Shell).
@[extern "lean_internal_set_max_memory"]
opaque setWorkerMaxMemory (bytes : USize) : BaseIO Unit

structure Config where
  mode : String := "validator"
  bounded : Bool := false
  steps : Nat := 100000
  inputsSpecified : Bool := false
  formatSpecified : Bool := false
  scripts : Array String := #[]
  format : String := "single_cbor_hex"
  leftFormat : Option String := none
  rightFormat : Option String := none
  language : String := "PlutusV3"
  inputs : String := "valid-context"
  equivalence : Bool := false
  budget : Option (Nat × Nat) := none
  timeout : Nat := 20
  wallTimeout : Nat := 180
  emitLean : Option String := none
  json : Bool := false
  worker : Bool := false
  caseIndex : Option Nat := none
  variation : String := "baseline"
  rawContext : Bool := false
  skipOldRejected : Bool := false

/-- Progress is separate from the final report, including in JSON mode. -/
def progress (message : String) : IO Unit := do
  let stderr ← IO.getStderr
  stderr.putStrLn s!"[uplc_equiv] {message}"
  stderr.flush

def specificVariationNames (choices : Array (String × String)) : String :=
  ", ".intercalate (choices.toList.filterMap fun (name, _) =>
    if Context.sharedVariations.any (fun variation => variation.name == name) then none else some name)

def usage : String := "Usage: lake exe uplc_equiv OLD NEW [options]

Validator mode checks that NEW accepts every input accepted by OLD within the supplied limits.
Function mode compares returned constants and success/error outcomes, ignoring execution costs.
  --mode validator|function                             Default validator; function defaults to integer inputs, no budget
  --steps N                                             Execution step limit; analysis guard unless --bounded (default 100000)
  --bounded                                             Compare observations within step/budget limits; OLD results/acceptance preserved
Budgeted checks use the bundled post-Conway cost model (V3: E; V1/V2: D).
  --inputs valid-context                                Validator default: generic V3 contexts; model-valid witnesses/replays, Data-superset proofs
  --inputs MODE                                         data (unrestricted Data), data3 (V2 arguments), integer
  --inputs spending                                     Generic spending context; arbitrary datum, redeemer, interval and lists
  --inputs htlc-refund|htlc-claim                       Restricted CAPE HTLC boundary domains (claim: fixed correct preimage)
  --inputs vesting-full|vesting-partial                 CAPE vesting domains (full: unbounded lists; partial: bounded inspected lists)
  --inputs escrow-deposit|escrow-accept|escrow-refund   CAPE escrow boundary domains
  --case N                                              Restrict the selected input mode to boundary case N
  --variation NAMES                                     Comma-separated variations, applied left to right (default baseline)
  --format FORMAT                                       textual, flat, flat_hex, single_cbor_hex (default), double_cbor_hex; .uplc paths default to textual
  --format-left FORMAT                                  Override the left script format
  --format-right FORMAT                                 Override the right script format
  --language VERSION                                    PlutusV1, PlutusV2, PlutusV3 (default)
  --budget CPU MEMORY                                   Shared execution-unit limits (required for strict validators; optional with --bounded or function mode)
  --equivalence                                         Check both directions (validators or --bounded functions)
  --skip-old-rejected                                   Skip the deferred OLD rejection query; OLD acceptance still needs a witness
  --timeout SECONDS                                     Z3 timeout per query (default 20)
  --wall-timeout SECONDS                                Limit the complete check, including preprocessing (default 180)
  --raw-context                                         Allow ledger-inconsistent HTLC/vesting/escrow contexts
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
Verification uses Blaster's SMT results without reconstructed Lean proof terms.\n\nShared variations: " ++
  ", ".intercalate (Context.sharedVariations.map Context.Variation.name)
  ++ "\nAvailability depends on the selected input mode."
  ++ "\n\nVesting variations: " ++ specificVariationNames Vesting.variations
  ++ "\n\nHTLC variations: " ++ specificVariationNames HTLC.variations
  ++ "\n\nEscrow variations: " ++ specificVariationNames Escrow.variations

def formats : List String := ["textual", "flat", "flat_hex", "single_cbor_hex", "double_cbor_hex"]

def isHtlcMode (mode : String) : Bool := mode == "htlc-refund" || mode == "htlc-claim"
def isVestingMode (mode : String) : Bool := mode == "vesting-full" || mode == "vesting-partial"
def isEscrowMode (mode : String) : Bool :=
  ["escrow-deposit", "escrow-accept", "escrow-refund"].contains mode

/-- Each scenario supplies one family entry point for both native and symbolic
    execution. The CLI does not need to construct scenario-specific case values. -/
structure Scenario where
  modes : Array String
  caseCount : String → Nat
  variations : Array (String × String)
  families : String → List String → Array (Context.GeneralFamily × Expr)

def registerScenario [ToExpr α] (modes : Array String) (cases : String → Array α)
    (variations : Array (String × String))
    (family : α → String → List String → Context.GeneralFamily) (declaration : Name) : Scenario :=
  { modes, variations, caseCount := fun mode => (cases mode).size,
    families := fun mode selection => (cases mode).map fun c =>
      (family c mode selection, mkApp3 (mkConst declaration) (toExpr c) (toExpr mode) (toExpr selection)) }

def scenarios : Array Scenario := #[
  registerScenario #["htlc-refund", "htlc-claim"] (fun _ => HTLC.cases)
    HTLC.variations HTLC.generalizedFamily ``HTLC.generalizedFamily,
  registerScenario #["vesting-full", "vesting-partial"] (fun mode => Vesting.cases (mode == "vesting-partial"))
    Vesting.variations Vesting.generalizedFamily ``Vesting.generalizedFamily,
  registerScenario #["escrow-deposit", "escrow-accept", "escrow-refund"] (fun _ => Escrow.cases)
    Escrow.variations Escrow.generalizedFamily ``Escrow.generalizedFamily]

def scenarioFor (mode : String) : Option Scenario :=
  scenarios.find? (fun scenario => scenario.modes.contains mode)

def isContextMode (mode : String) : Bool := (scenarioFor mode).isSome

def checksLedger (c : Config) : Bool :=
  c.inputs == "valid-context" || (isContextMode c.inputs && !c.rawContext)

def validLedgerContext (c : Config) (raw : PlutusCore.Data.Data) : Bool :=
  if c.inputs == "valid-context" then Ledger.validScriptContext raw else Ledger.validContext raw

def auditLedgerContext (c : Config) (raw : PlutusCore.Data.Data) : Json :=
  Ledger.audit raw (c.inputs != "valid-context")

def caseCount (mode : String) : Nat :=
  ((scenarioFor mode).map (fun scenario => scenario.caseCount mode)).getD 0

def variationChoices (mode : String) : Array (String × String) :=
  ((scenarioFor mode).map Scenario.variations).getD
    (Context.baselineGroup.toArray.map Context.Variation.describe)

def natOption (key value : String) (positive := false) : Except String Nat := do
  let some n := value.toNat? | throw s!"{key} expects a nonnegative integer"
  if positive && n == 0 then throw s!"{key} must be positive"
  return n

def parse (c : Config) : List String → Except String Config
  | [] => do
    unless c.scripts.size == 2 do throw "expected old and new script paths"
    unless ["validator", "function"].contains c.mode do throw s!"unsupported mode: {c.mode}"
    let c := if c.mode == "function" && !c.inputsSpecified && c.inputs == "valid-context" then
      { c with inputs := "integer" } else c
    let c := if c.formatSpecified then c else
      { c with
        leftFormat := c.leftFormat.orElse fun _ => if c.scripts[0]!.endsWith ".uplc" then some "textual" else none
        rightFormat := c.rightFormat.orElse fun _ => if c.scripts[1]!.endsWith ".uplc" then some "textual" else none }
    if c.mode == "validator" && !c.bounded && c.budget.isNone then
      throw "validator checking requires --budget CPU MEMORY or --bounded --steps N"
    if c.mode == "function" then
      unless ["integer", "data", "data3"].contains c.inputs do
        throw "function mode supports --inputs integer, data or data3"
      if c.equivalence && !c.bounded then
        throw "function --equivalence requires --bounded; strict function mode already compares both outcomes"
      if c.skipOldRejected || c.rawContext then
        throw "--skip-old-rejected and --raw-context are validator options"
    unless ["integer", "data", "data3", "spending", "valid-context"].contains c.inputs || isContextMode c.inputs do throw s!"unsupported input mode: {c.inputs}"
    if c.inputs == "valid-context" then
      if c.rawContext then throw "--inputs valid-context cannot be combined with --raw-context; use --inputs data for raw Data"
      if c.language != "PlutusV3" then throw "--inputs valid-context requires --language PlutusV3"
    if let some index := c.caseIndex then
      unless isContextMode c.inputs do throw "--case requires a contract input mode"
      unless index < caseCount c.inputs do throw "--case is outside the selected mode's case range"
    for variation in Context.variationNames c.variation do
      unless (variationChoices c.inputs).any (fun entry => entry.1 == variation) do
        throw s!"unsupported variation for {c.inputs}: {variation}"
    if c.inputs == "spending" && c.language != "PlutusV3" then
      throw "--inputs spending requires --language PlutusV3"
    if isContextMode c.inputs && !c.rawContext && c.language != "PlutusV3" then
      throw "ledger-model context checks require --language PlutusV3; use --raw-context for other languages"
    unless ["PlutusV1", "PlutusV2", "PlutusV3"].contains c.language do
      throw s!"unsupported language: {c.language}"
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
  | "--raw-context" :: rest => parse { c with rawContext := true } rest
  | "--skip-old-rejected" :: rest => parse { c with skipOldRejected := true } rest
  | "--format" :: v :: rest => parse { c with format := v, formatSpecified := true } rest
  | "--format-left" :: v :: rest => parse { c with leftFormat := some v } rest
  | "--format-right" :: v :: rest => parse { c with rightFormat := some v } rest
  | "--language" :: v :: rest => parse { c with language := v } rest
  | "--inputs" :: v :: rest => parse { c with inputs := v, inputsSpecified := true } rest
  | "--case" :: v :: rest => do parse { c with caseIndex := some (← natOption "--case" v) } rest
  | "--variation" :: v :: rest => parse { c with variation := v } rest
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
    let (noRegression, preserved) :=
      if c.inputs == "spending" then
        (``Context.spendingNoAcceptanceRegression, ``Context.spendingAcceptancePreserved)
      else if isContextMode c.inputs then
        (``Context.generalizedNoAcceptanceRegression, ``Context.generalizedAcceptancePreserved)
      else if c.inputs == "data" || c.inputs == "valid-context" then
        (``Queries.contextNoAcceptanceRegression, ``Queries.contextAcceptancePreserved)
      else if c.inputs == "data3" then
        (``Queries.validatorNoAcceptanceRegression, ``Queries.validatorAcceptancePreserved)
      else
        (``Queries.integerNoAcceptanceRegression, ``Queries.integerAcceptancePreserved)
    let forward : Array Query := #[
      ⟨"acceptance_preserved", preserved, #[0, 1]⟩,
      ⟨"no_acceptance_regression", noRegression, #[0, 1]⟩]
    let rejectedDeclaration :=
      if c.inputs == "spending" then ``Context.spendingRejected
      else if isContextMode c.inputs then ``Context.generalizedRejected
      else if c.inputs == "data" || c.inputs == "valid-context" then ``Queries.contextRejected
      else if c.inputs == "data3" then ``Queries.validatorRejected
      else ``Queries.integerRejected
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

def vestingCases (c : Config) : Array Vesting.Case :=
  let choices := Vesting.cases (c.inputs == "vesting-partial")
  match c.caseIndex with
  | none => choices
  | some index => choices[index]?.toArray

def htlcCases (c : Config) : Array HTLC.Case :=
  match c.caseIndex with
  | none => HTLC.cases
  | some index => HTLC.cases[index]?.toArray

def escrowCases (c : Config) : Array Escrow.Case :=
  match c.caseIndex with
  | none => Escrow.cases
  | some index => Escrow.cases[index]?.toArray

def baseInputDomain (c : Config) : String :=
  if c.inputs == "integer" then "all integers, encoded as raw UPLC integer constants"
  else if c.inputs == "valid-context" then
    "Generic V3 script contexts satisfying the ledger model's validScriptContext predicate, for all script purposes; no contract template; concrete model-valid domain and OLD-acceptance witnesses and counterexample replays required; preservation is proved over the unrestricted Data superset because symbolic ledger filtering is unavailable; model validity does not establish on-chain reachability"
  else if c.inputs == "spending" then
    "Generic V3 spending context: constructor 0 with a 16-field TxInfo, arbitrary redeemer and spending ScriptInfo; arbitrary-length independent input, reference-input, output and signer lists; arbitrary nested Data; nonnegative integer fee; map/list/bytes outer encodings for the other common TxInfo fields; independent arbitrary Data for the interval, spending reference, datum option, treasury and donation; no fixed keys, assets, amounts, schedule or boundary cases; no ledger-validity restriction on nested Data or transaction relationships"
  else if isEscrowMode c.inputs then
    let selected := match c.caseIndex, (escrowCases c)[0]? with
      | some index, some choice =>
        s!"; restricted to case {index}: time offset {choice.time.value - 100}, signed={choice.signed}, amount delta={choice.amountDelta}, hasTreasury={choice.hasTreasury}, hasDonation={choice.hasDonation}"
      | _, _ => ""
    s!"CAPE two-party escrow {c.inputs}: price 75000000 lovelace; deposit time 1000000, deadline 2800000; amount price-1/price/price+1; one own escrow input, a separate funding input and one output; fixed keys, ASCII script hash, references and Deposited datum; raw integer redeemer; no signer or required signer first with arbitrary Data tail; Deposit upper endpoint 1000000/1000001/1000002 (exclusive), arbitrary lower endpoint; Accept/Refund lower endpoint 2799999/2800000/2800001, arbitrary upper endpoint" ++ selected
  else if c.inputs == "htlc-claim" then
    "CAPE HTLC claim template: effective upper timestamp 99/100/101, arbitrary integer lower timestamp; one own input and optional second same-address input; zero or one recipient signature; fixed correct preimage, datum (timeout 100), references, addresses; unused fields share the typed outer encodings described below"
  else if c.inputs == "htlc-refund" then
    "CAPE HTLC refund template: lower timestamp 99/100/101, arbitrary integer upper timestamp; one own input and optional second same-address input; zero or one payer signature; fixed datum (timeout 100), references, addresses; unused fields share the typed outer encodings described below"
  else if isVestingMode c.inputs then
    let operation := if c.inputs == "vesting-full" then
      "full unlock: lower timestamp 99/100/101, arbitrary-length input and output lists of arbitrary Data"
    else "partial unlock: lower timestamp 9/10/11, one own input and optional second same-address input, one continuing output with quantity 900 or 901 and preserved datum"
    let selected := match c.caseIndex, (vestingCases c)[0]? with
      | some index, some choice =>
        let lower := choice.time.value - (if c.inputs == "vesting-partial" then 90 else 0)
        let partialFields := if c.inputs == "vesting-partial" then
          s!", doubleInput={choice.doubleInput}, correctQuantity={choice.correctQuantity}" else ""
        s!"; restricted to case {index}: lower timestamp {lower}, signed={choice.signed}{partialFields}, hasTreasury={choice.hasTreasury}, hasDonation={choice.hasDonation}"
      | _, _ => ""
    "CAPE linear vesting " ++ operation ++ selected ++
      "; arbitrary integer upper timestamp; no signatories or beneficiary first with arbitrary-length Data tail; " ++
      "fixed beneficiary, asset, references, addresses, and datum " ++
      "(total 1000, schedule 0..100, first unlock after 10, ten installments)"
  else if c.inputs == "data" then "all Plutus Data values as a single script-context argument, without ledger-validity restrictions"
  else "all triples of Plutus Data (datum, redeemer, context), without ledger-validity restrictions"

def inputDomain (c : Config) : String :=
  let base := if c.mode == "function" && c.inputs == "data" then
    "all Plutus Data values as a single function argument"
    else if c.mode == "function" && c.inputs == "data3" then
      "all triples of Plutus Data as function arguments"
    else if !isHtlcMode c.inputs then baseInputDomain c else
    match c.caseIndex, (htlcCases c)[0]? with
    | some index, some choice =>
      baseInputDomain c ++ s!"; restricted to case {index}: boundary timestamp {choice.time.value}, signed={choice.signed}, doubleInput={choice.doubleInput}, hasTreasury={choice.hasTreasury}, hasDonation={choice.hasDonation}"
    | _, _ => baseInputDomain c
  let base := if isContextMode c.inputs then
    base ++ "; shared list/map/bytestring/integer outer encodings; nonnegative fee and treasury/donation amounts; " ++
      "unbounded unused list/map contents and signature tail; " ++
      (if c.rawContext then "raw context mode: ledger validity is not required"
       else "ledger-model checks require a concrete valid-domain witness and valid counterexample replays; preservation is proved over the raw-context superset")
    else base
  let variation := c.variation
  let choices := variationChoices c.inputs
  if variation == "baseline" then base
  else
    let description := "; then ".intercalate ((Context.variationNames variation).map fun name =>
      ((choices.find? (fun entry => entry.1 == name)).map Prod.snd).getD "unknown")
    s!"Exploratory context variation: {variation}: {description}. " ++
      "Variations override the restrictions they change; later writes to the same field win. " ++
      "Base template before replacement: " ++ base

def status : Blaster.Smt.Result → String
  | .Valid => "valid"
  | .Falsified _ => "falsified"
  | .Undetermined => "undetermined"

/-- Select concrete cases and parse composition before symbolic translation. -/
def selectedFamilies (c : Config) : Array (Context.GeneralFamily × Expr) :=
  match scenarioFor c.inputs with
  | some scenario =>
    let families := scenario.families c.inputs (Context.variationNames c.variation)
    match c.caseIndex with
    | some index => families[index]?.toArray
    | none => families
  | none => #[]

def contextFamilies (c : Config) : Array Context.GeneralFamily := (selectedFamilies c).map Prod.fst

/-- A bounded search can establish nonemptiness, never emptiness. Each candidate
    is rebuilt through the actual family so mutations are not silently repaired. -/
def nativeDomainWitness (c : Config)
    (matchesCandidate : PlutusCore.Data.Data → Bool := fun _ => true) : Option PlutusCore.Data.Data := Id.run do
  if c.inputs == "valid-context" then
    return if Ledger.validScriptContext Context.genericValidContext && matchesCandidate Context.genericValidContext then
      some Context.genericValidContext else none
  let input := if isVestingMode c.inputs then Vesting.ownInput
    else if isEscrowMode c.inputs then Escrow.ownInput else HTLC.ownInput
  let general : Context.GeneralFields := {
    lower := 0, upper := 3000000, datum := .I 0, redeemer := .I 0,
    reference := Context.ownRef, interval := Context.range 0 3000000 }
  for family in contextFamilies c do
    for timestamp in [0, 200, 3000000] do
      let seed : Context.UnusedTxInfo := { fee := 1, treasury := 1, donation := 1 }
      let [.Const (.Data initial)] := family general seed [input] [] [] timestamp | continue
      let some initialBalance := Ledger.balancing initial | continue
      let changeValue := CardanoLedgerApi.V2.add "" "" (-1) initialBalance.spent
      let change := Context.txOutput
        (Context.pubKeyAddress ⟨String.mk (List.replicate 28 'c')⟩) (.Map changeValue)
      for outputs in [[], [change]] do
        let seed := { seed with rawUnused := { seed.rawUnused with outputs := .List outputs } }
        let [.Const (.Data raw)] := family general seed [input] outputs [] timestamp | continue
        let some balance := Ledger.balancing raw | continue
        if balance.fee ≤ 0 then continue
        let unused := { seed with
          fee := balance.fee
          mint := balance.mint
          rawUnused := { seed.rawUnused with
            fee := .I balance.fee
            mint := .Map balance.mint
            redeemers := balance.redeemers } }
        let [.Const (.Data candidate)] := family general unused [input] outputs [] timestamp | continue
        if Ledger.validContext candidate && matchesCandidate candidate then return some candidate
  return none

def contextFamilyExprs (c : Config) : Array Expr := (selectedFamilies c).map Prod.snd

def queryPropositions (c : Config) (query : Query) (programs : Array Expr)
    (families : Array Expr := contextFamilyExprs c) : Array Expr :=
  let (cpu, memory) := c.budget.getD (0, 0)
  let limits := #[mkRawNatLit cpu, mkRawNatLit memory, toExpr (c.language == "PlutusV3")]
  let limits := if c.mode == "function" then limits ++ #[toExpr c.budget.isSome, mkRawNatLit c.steps] else
    limits ++ #[toExpr c.bounded, toExpr c.budget.isSome, mkRawNatLit c.steps]
  let arguments := query.sides.map (programs[·]!) ++ limits
  if families.isEmpty then #[mkAppN (mkConst query.declaration) arguments]
  else families.map fun family => mkAppN (mkConst query.declaration) (#[family] ++ arguments)

/-- Every selected input family must preserve acceptance. -/
def combineResults (left right : Blaster.Smt.Result) : Blaster.Smt.Result :=
  match left, right with
  | .Falsified model, _ | _, .Falsified model => .Falsified model
  | .Valid, .Valid => .Valid
  | _, _ => .Undetermined

/-- Erase fixture/catalog plumbing before Blaster sees the family. Execution
    itself is left to Blaster; only the context-building function is reduced. -/
def prepareContextFamilies (env : Environment) (c : Config) : IO (Array Expr) := do
  let action : MetaM (Array Expr) :=
    (contextFamilyExprs c).mapM (fun family => Meta.reduce family (explicitOnly := false))
  let (families, _) ← action.run' |>.toIO
    { fileName := "<uplc_equiv>", fileMap := default, maxRecDepth := 0, maxHeartbeats := 0 } { env }
  -- Widening can erase case distinctions. Solve each remaining family once.
  return families.foldl (fun unique family =>
    if unique.contains family then unique else unique.push family) #[]

def report (verdict explanation : String) (fields : List (String × Json) := []) : Json :=
  Json.mkObj ([("verdict", toJson verdict), ("explanation", toJson explanation)] ++ fields)

/-- Blaster returns model values as strings, e.g. `n: (- 42)\n`.
    Callers with multiple integer parameters also match their binder names. -/
def modelInteger (binding : String) : Option Int :=
  (Model.integerBinding binding).map Prod.snd

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
  Json.mkObj (("accepts", toJson (Acceptance.accepts v3 (Validator.observe bounded result))) :: fields)

def functionOutcomeJson (budgeted : Bool) (result : Acceptance.Result) : Json :=
  match result with
  | .success value spent => Json.mkObj ([("kind", toJson "success"), ("result", valueJson value)] ++
      (if budgeted then [("spent_cpu", toJson spent.exBudgetCPU.unExCPU),
        ("spent_memory", toJson spent.exBudgetMemory.unExMemory)] else []))
  | .error => Json.mkObj [("kind", toJson "error")]
  | .budgetExhausted => Json.mkObj [("kind", toJson "budget_exhausted")]
  | .unfinished => Json.mkObj [("kind", toJson "unfinished")]

/-- Reconstruct each independently quantified unused field from its SMT binding.
    Unmentioned fields use the original minimal context, including simplified
    queries for which the optimizer produces no model. -/
def modelContextUnusedTxInfo (model : List String) : Context.UnusedTxInfo :=
  let lists := model.filterMap Model.listBinding
  let maps := model.filterMap Model.mapBinding
  let integers := model.filterMap Model.integerBinding
  let bytes := model.filterMap Model.byteStringBinding
  let raw := model.filterMap Model.dataBinding
  let defaults : Context.RawUnusedTxInfo := {}
  { referenceInputs := (lists.lookup "referenceInputs").getD []
    fee := (integers.lookup "fee").getD 0
    mint := (maps.lookup "mint").getD []
    certificates := (lists.lookup "certificates").getD []
    withdrawals := (maps.lookup "withdrawals").getD []
    redeemers := (maps.lookup "redeemers").getD []
    datums := (maps.lookup "datums").getD []
    txId := (bytes.lookup "txId").getD "tx"
    votes := (maps.lookup "votes").getD []
    proposals := (lists.lookup "proposals").getD []
    treasury := (integers.lookup "treasury").getD 0
    donation := (integers.lookup "donation").getD 0
    rawUnused := {
      referenceInputs := (raw.lookup "rawReferenceInputs").getD defaults.referenceInputs
      outputs := (raw.lookup "rawOutputs").getD defaults.outputs
      fee := (raw.lookup "rawFee").getD defaults.fee
      mint := (raw.lookup "rawMint").getD defaults.mint
      certificates := (raw.lookup "rawCertificates").getD defaults.certificates
      withdrawals := (raw.lookup "rawWithdrawals").getD defaults.withdrawals
      redeemers := (raw.lookup "rawRedeemers").getD defaults.redeemers
      datums := (raw.lookup "rawDatums").getD defaults.datums
      txId := (raw.lookup "rawTxId").getD defaults.txId
      votes := (raw.lookup "rawVotes").getD defaults.votes
      proposals := (raw.lookup "rawProposals").getD defaults.proposals
      treasury := (raw.lookup "rawTreasury").getD defaults.treasury
      donation := (raw.lookup "rawDonation").getD defaults.donation } }

def modelGeneralFields (model : List String) : Context.GeneralFields :=
  let integers := model.filterMap Model.integerBinding
  let data := model.filterMap Model.dataBinding
  { lower := (integers.lookup "lowerTimestamp").getD 0
    upper := (integers.lookup "upperTimestamp").getD 0
    datum := (data.lookup "arbitraryDatum").getD (.I 0)
    redeemer := (data.lookup "arbitraryRedeemer").getD (.I 0)
    interval := (data.lookup "arbitraryInterval").getD (.I 0)
    reference := (data.lookup "arbitraryReference").getD (.I 0) }

def modelFamilyArguments (c : Config) (model : List String) : List (List PlutusCore.UPLC.Term.Term) := Id.run do
  let lists := model.filterMap Model.listBinding
  let inputs := (lists.lookup "inputs").getD []
  let outputs := (lists.lookup "outputs").getD []
  let signatureTail := (lists.lookup "signatureTail").getD []
  let general := modelGeneralFields model
  let timestamps := ((model.filterMap Model.integerBinding).lookup "timestamp").toList ++ [0]
  let mut candidates := []
  for unused in [modelContextUnusedTxInfo model, {}] do
    if unused.fee < 0 || unused.treasury < 0 || unused.donation < 0 then continue
    for timestamp in timestamps do
      for family in contextFamilies c do
        candidates := family general unused inputs outputs signatureTail timestamp :: candidates
  return candidates.reverse

/-- A solver witness is only advertised as replayed after native CEK execution
    reproduces the acceptance difference under the shared budget. -/
def replayWitness (c : Config) (left right : PlutusCore.UPLC.Term.Program)
    (model : List String) (reverse := false) (acceptanceOnly := false) : Json := Id.run do
  let (cpu, memory) := c.budget.getD (0, 0)
  let v3 := c.language == "PlutusV3"
  let replay := fun args input => do
    let execute := fun program => Function.execute program args cpu memory v3 c.budget.isSome c.steps
    let old := execute left
    let new := execute right
    let oldObserved := Validator.observe c.bounded old
    let newObserved := Validator.observe c.bounded new
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
    else replay args (Model.dataJson context)
  -- Optimization can reduce a universally false query to False without asking
  -- Z3 for a model. Try zero inputs too, but still require a successful replay.
  let families := contextFamilies c
  if c.inputs == "spending" || !families.isEmpty then
    let lists := model.filterMap Model.listBinding
    let inputs := (lists.lookup "inputs").getD []
    let outputs := (lists.lookup "outputs").getD []
    let signatureTail := (lists.lookup "signatureTail").getD []
    let unused := modelContextUnusedTxInfo model
    if c.inputs == "spending" then
      let bindings := model.filterMap Model.dataBinding
      let find := fun name => (bindings.lookup name).getD (.I 0)
      let family := Context.spendingFamily (find "spendingReference") (find "spendingDatumOption")
        (find "spendingRedeemer") (find "validRange") (find "treasuryField") (find "donationField")
      if let some witness := replayContext (family unused inputs outputs signatureTail 0) then
        return witness
    else
      for args in modelFamilyArguments c model do
        if let some witness := replayContext args then return witness
      if !c.rawContext then
        -- A valid context need not be accepted by this script (the first
        -- template case is often unsigned). Keep searching all selected
        -- families until the candidate also reproduces the desired outcome.
        let candidate := nativeDomainWitness c fun raw =>
          (replayContext (Queries.contextArgs raw)).isSome
        if let some context := candidate then
          if let some witness := replayContext (Queries.contextArgs context) then return witness
  else if c.inputs == "data" || c.inputs == "valid-context" then
    let candidates := (model.filterMap Model.dataBinding).map Prod.snd ++ [.I 0] ++
      (if checksLedger c then (nativeDomainWitness c).toList else [])
    for context in candidates do
      if let some witness := replayContext (Queries.contextArgs context) then
        return witness
  else if c.inputs == "data3" then
    let bindings := model.filterMap Model.dataBinding
    let find := fun name => bindings.lookup name
    let zero := PlutusCore.Data.Data.I 0
    let candidates := [((find "datum").getD zero, (find "redeemer").getD zero, (find "context").getD zero),
      (zero, zero, zero)]
    for (datum, redeemer, context) in candidates do
      let input := Json.mkObj [("datum", Model.dataJson datum),
        ("redeemer", Model.dataJson redeemer), ("context", Model.dataJson context)]
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
    (caseResults : Option (IO.Ref (Array (Array Blaster.Smt.Result))) := none)
    (preparedFamilies : Option (Array Expr) := none) : IO (Array Blaster.Smt.Result) := do
  let families ← match preparedFamilies with
    | some families => pure families
    | none => prepareContextFamilies env c
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
        if let some ref := caseResults then ref.modify (·.push #[])
        continue
      let mut checked := #[]
      let mut combined : Blaster.Smt.Result := .Valid
      progress s!"Starting: {query.description} [{query.name}]"
      let propositions := queryPropositions c query programs families
      for (proposition, index) in propositions.toList.zipIdx do
        if propositions.size > 1 then
          progress s!"Starting: {query.name}, case {index + 1}/{propositions.size}"
        let solverEnv := { (default : Blaster.Optimize.TranslateEnv) with
          optEnv.options.solverOptions.timeout := some c.timeout
          optEnv.options.solverOptions.generateCex := query.wantsCounterexample }
        let ((result, _), _) ← Blaster.Smt.Translate.main proposition |>.run solverEnv
        checked := checked.push result
        combined := combineResults combined result
        match combined with
        | .Falsified _ => break
        | _ => pure ()
      if let some ref := caseResults then ref.modify (·.push checked)
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
            if let some ref := caseResults then ref.modify (fun rows => rows.set! i #[])
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
    ("steps", toJson c.steps),
    ("budget", c.budget.map (fun (cpu, memory) => Json.mkObj [("cpu", toJson cpu), ("memory", toJson memory)]) |>.getD Json.null)]
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
          ("proof_domain", toJson (if c.inputs == "valid-context" then "unrestricted Data overapproximation" else "raw-context overapproximation")),
          ("domain_witness", Model.dataJson raw), ("ledger_validity", auditLedgerContext c raw)]
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
      -- Every CLI domain supplies at least one argument, hence its initial
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
    ("mode", toJson "validator"), ("bounded", toJson c.bounded), ("steps", toJson c.steps),
    ("check", toJson (if c.equivalence then "acceptance preservation in both directions" else "old acceptance implies new acceptance")),
    ("budget", c.budget.map (fun (cpu, memory) => Json.mkObj [("cpu", toJson cpu), ("memory", toJson memory)]) |>.getD Json.null),
    ("language", toJson c.language)] ++
    (if c.budget.isSome then [("cost_model", toJson (if c.language == "PlutusV3" then "bundled post-Conway E" else "bundled post-Conway D"))]
     else [("execution", toJson "uncosted")])
  let counterexample := regression.toList.map fun (reverse, model) =>
    ("counterexample", replayCounterexample c left right model reverse)
  if checksLedger c then
    for (_, witness) in counterexample do
      unless replayConfirmed witness do
        return report "inconclusive" "The raw countermodel could not be replayed as a ledger-valid acceptance regression."
          (ledgerFields ++ [("input_domain", toJson (inputDomain c)), ("diagnostic_counterexample", witness)])
  let derivations := (queries c).toList.filterMap fun query =>
    (queryEvidence c query results).map fun evidence => (query.name, toJson evidence)
  let provenance := if derivations.isEmpty then [] else [("derived_queries", Json.mkObj derivations)]
  return report verdict explanation ([("input_domain", toJson (inputDomain c))] ++ details ++ ledgerFields ++ acceptanceFields ++ [
    ("queries", Json.mkObj (names.toList.zip (results.toList.map (toJson ∘ status)))),
    ("verification", toJson "Blaster SMT result; no reconstructed Lean proof term")] ++ provenance ++ counterexample)

def sourceHeader (c : Config) : IO String := do
  let left ← IO.FS.realPath c.scripts[0]!
  let right ← IO.FS.realPath c.scripts[1]!
  return s!"import Equivalence.Queries\nimport Equivalence.HTLC\nimport Equivalence.Vesting\nimport Equivalence.Escrow\nimport Blaster\nopen Equivalence.Queries\n#import_uplc left {c.language} {c.leftFormat.getD c.format} {toJson left.toString |>.compress}\n#import_uplc right {c.language} {c.rightFormat.getD c.format} {toJson right.toString |>.compress}\n"

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

def emitSource (env : Environment) (c : Config) (caseResults : Array (Array Blaster.Smt.Result) := #[])
    (families : Array Expr := contextFamilyExprs c) : IO Unit := do
  let some file := c.emitLean | return
  let header ← sourceHeader c
  let project := fun name => mkApp (mkConst ``PlutusCore.UPLC.PlutusScript.PlutusScript.script) (mkConst name)
  let programs := #[project `left, project `right]
  let chunks ← (queries c).toList.zipIdx.flatMapM fun (query, i) =>
    (queryPropositions c query programs families).toList.zipIdx.filterMapM fun (proposition, j) => do
      -- Match each checked case's actual result, including false existence
      -- cases. Short-circuited cases need not be rerun to reproduce the verdict.
      let expected := if caseResults.isEmpty then some "" else do
        let checked ← caseResults[i]?
        let result ← checked[j]?
        let code := match result with
          | .Valid => 0
          | .Falsified _ => 1
          | .Undetermined => 2
        some s!" (solve-result: {code})"
      let some expected := expected | return none
      let action : MetaM Format := do
        -- These names are supplied by #import_uplc in the emitted module.
        let scriptType := mkConst ``PlutusCore.UPLC.PlutusScript.PlutusScript
        Meta.withLocalDeclD `left scriptType fun left =>
          Meta.withLocalDeclD `right scriptType fun right => do
            let proposition := proposition.replace fun e => match e with
              | .const `left _ => some left
              | .const `right _ => some right
              | _ => none
            PrettyPrinter.ppExpr proposition
      let (rendered, _) ← action.run' |>.toIO
        { fileName := "<uplc_equiv>", fileMap := default, maxRecDepth := 0, maxHeartbeats := 0 } { env }
      return some s!"\n-- {query.name}, case {j + 1}\n#blaster (timeout: {c.timeout}){expected} (gen-cex: {if query.wantsCounterexample then 1 else 0}) [{rendered.pretty}]\n"
  let scope := if checksLedger c then
    "\n-- These queries prove preservation over the raw-context superset.\n-- The CLI separately checks a native ledger-model-valid domain witness\n-- and validates counterexample replays; those checks are not reproduced here.\n"
    else ""
  IO.FS.writeFile file (header ++
    (if c.mode == "function" then "\n-- Function countermodels are separately replayed by the CLI.\n" else
      "\n-- The CLI separately replays an OLD-accepting input before reporting\n-- nonvacuous preservation. These queries alone do not reproduce that replay.\n") ++
    scope ++ String.join chunks)

def run (c : Config) : IO Json := do
  let c ← IO.ofExcept (parse c [])
  progress "Starting: loading OLD script"
  let left ← readProgram c.scripts[0]! (c.leftFormat.getD c.format)
  progress "Starting: loading NEW script"
  let right ← readProgram c.scripts[1]! (c.rightFormat.getD c.format)
  if c.mode == "function" && decide (left = right) then
    progress "Finished: program_identity: identical decoded UPLC programs"
    if c.emitLean.isSome then
      progress "Starting: exporting program-identity proof"
      emitIdenticalSource c
    return classifyFunction c #[] left right
  if checksLedger c then progress "Starting: constructing a ledger-model-valid domain witness"
  let domainWitness := if checksLedger c then nativeDomainWitness c else none
  if checksLedger c && domainWitness.isNone then
    return report "inconclusive" "Could not construct a ledger-valid context witnessing the selected domain; no preservation claim is made."
      [("domain_status", toJson "unestablished"), ("input_domain", toJson (inputDomain c))]
  if checksLedger c then progress "Finished: ledger-model-valid domain witness constructed"
  -- Keep working when the binary is invoked outside the repository or without `lake env`.
  progress "Starting: preparing symbolic checker"
  initSearchPath toolchainRoot (moduleSearchPath.map FilePath.mk)
  let env ← importModules #[{ module := `Equivalence.Queries }, { module := `Equivalence.HTLC }, { module := `Equivalence.Vesting }, { module := `Equivalence.Escrow }, { module := `Blaster }] {} (loadExts := true)
  progress "Starting: preparing symbolic input families"
  let families ← prepareContextFamilies env c
  if c.emitLean.isSome then progress "Starting: exporting initial Lean queries"
  emitSource env c #[] families
  let caseResults ← IO.mkRef #[]
  if c.skipOldRejected then progress "Skipping: old_rejected (--skip-old-rejected)"
  let results ← solve env c left right (some caseResults) (some families)
  if c.emitLean.isSome then progress "Starting: exporting checked Lean queries"
  emitSource env c (← caseResults.get) families
  progress "Starting: validating replay witnesses and classifying results"
  return classify c results left right domainWitness

partial def waitUntil (child : IO.Process.Child cfg) (deadline : Nat) : IO Bool := do
  if (← child.tryWait).isSome then return true
  if (← IO.monoMsNow) ≥ deadline then
    child.kill
    discard child.wait
    return false
  IO.sleep 50
  waitUntil child deadline

/-- Forward worker diagnostics immediately, retaining them for malformed reports. -/
def forwardDiagnostics (source : IO.FS.Handle) : IO String := do
  let target ← IO.getStderr
  let mut captured := ""
  repeat
    let line ← source.getLine
    if line.isEmpty then break
    target.putStr line
    target.flush
    captured := captured ++ line
  return captured

/-- A second instance of this native executable isolates the checker so the parent
    can stop preprocessing and its Z3 children at the wall-clock deadline. -/
def supervise (args : List String) (c : Config) : IO Json := do
  let child ← IO.Process.spawn {
    cmd := (← IO.appPath).toString
    args := ("--worker" :: args).toArray
    setsid := true
    stdin := .null
    stdout := .piped
    stderr := .piped }
  let output ← IO.asTask child.stdout.readToEnd
  let errors ← IO.asTask (forwardDiagnostics child.stderr)
  let finished ← waitUntil child ((← IO.monoMsNow) + c.wallTimeout * 1000)
  let stdout ← IO.ofExcept output.get
  let stderr ← IO.ofExcept errors.get
  unless finished do
    return report "inconclusive" s!"Wall-clock limit of {c.wallTimeout}s reached; preprocessing or solving did not finish."
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
      IO.println s!"Step limit: {steps}"
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
    if let .ok witness := r.getObjVal? "counterexample" then
      IO.println s!"Counterexample:\n{witness.pretty}"
    if (r.getObjVal? "old_acceptance_witness").isOk then
      IO.println "OLD acceptance: confirmed by native replay (input available with --json)"

end Equivalence.Cli

open Equivalence.Cli

def main (args : List String) : IO UInt32 := do
  -- Test workers share Lean's memory guard without adding public CLI options.
  if (← IO.getEnv "UPLC_EQUIV_TEST_WORKER") == some "1" then
    setWorkerMaxMemory (8192 * 1024 * 1024)
  if args.contains "--help" || args.contains "-h" then
    IO.println usage
    return 0
  else
    let parsed := parse {} args
    let config := parsed.toOption.getD { json := args.contains "--json" }
    let result ← try
      match parsed with
      | .error error => pure (report "error" error)
      | .ok c => if c.worker then run c else supervise args c
    catch error => pure (report "error" error.toString)
    printReport config.json result
    return exitCode result
