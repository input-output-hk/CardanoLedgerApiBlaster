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

-- Same runtime guard used by Lean's --memory option (private in Lean.Shell).
@[extern "lean_internal_set_max_memory"]
opaque setWorkerMaxMemory (bytes : USize) : BaseIO Unit

structure Config where
  scripts : Array String := #[]
  format : String := "single_cbor_hex"
  leftFormat : Option String := none
  rightFormat : Option String := none
  language : String := "PlutusV3"
  inputs : String := "integer"
  steps : Nat := 1000
  leftSteps : Option Nat := none
  rightSteps : Option Nat := none
  timeout : Nat := 20
  wallTimeout : Nat := 180
  emitLean : Option String := none
  json : Bool := false
  worker : Bool := false
  caseIndex : Option Nat := none
  variation : String := "baseline"

def specificVariationNames (choices : Array (String × String)) : String :=
  ", ".intercalate (choices.toList.filterMap fun (name, _) =>
    if Context.sharedVariations.any (fun variation => variation.name == name) then none else some name)

def usage : String := "Usage: lake exe uplc_equiv SCRIPT1 SCRIPT2 [options]

Compare UPLC functions or validators using Blaster.
  --inputs MODE                                        integer (default), data (V3 context), data3 (V2 arguments)
  --inputs htlc-refund|htlc-claim                      Restricted CAPE HTLC boundary domains (claim: fixed correct preimage)
  --inputs vesting-full|vesting-partial                CAPE vesting domains (full: unbounded lists; partial: bounded inspected lists)
  --inputs escrow-deposit|escrow-accept|escrow-refund  CAPE escrow boundary domains
  --case N                                             Restrict the selected input mode to boundary case N
  --variation NAMES                                    Comma-separated variations, applied left to right (default baseline)
  --format FORMAT                                      textual, flat, flat_hex, single_cbor_hex (default), double_cbor_hex
  --format-left FORMAT                                 Override the left script format
  --format-right FORMAT                                Override the right script format
  --language VERSION                                   PlutusV1, PlutusV2, PlutusV3 (default)
  --max-steps N                                        Execution fuel for each script (default 1000)
  --left-steps N                                       Override the left execution fuel
  --right-steps N                                      Override the right execution fuel
  --timeout SECONDS                                    Z3 timeout per query (default 20)
  --wall-timeout SECONDS                               Limit the complete check, including preprocessing (default 180)
  --emit-lean FILE                                     Save equivalent Lean queries for inspection
  --json                                               Emit a JSON report
  --help                                               Show this help

Exit codes: 0 equivalent, 1 inequivalent, 2 inconclusive, 3 tool/usage error.
Shared-output agreement alone does not establish termination or full equivalence.
Fuel exhaustion is inconclusive; matching actual execution errors are equivalent.
Counterexamples include the input and both outcomes, replayed with the configured fuel.
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
  families : String → List String → Array (Context.Family × Expr)

def registerScenario [ToExpr α] (modes : Array String) (cases : String → Array α)
    (variations : Array (String × String))
    (family : α → String → List String → Context.Family) (declaration : Name) : Scenario :=
  { modes, variations, caseCount := fun mode => (cases mode).size,
    families := fun mode selection => (cases mode).map fun c =>
      (family c mode selection, mkApp3 (mkConst declaration) (toExpr c) (toExpr mode) (toExpr selection)) }

def scenarios : Array Scenario := #[
  registerScenario #["htlc-refund", "htlc-claim"] (fun _ => HTLC.cases)
    HTLC.variations HTLC.family ``HTLC.family,
  registerScenario #["vesting-full", "vesting-partial"] (fun mode => Vesting.cases (mode == "vesting-partial"))
    Vesting.variations Vesting.family ``Vesting.family,
  registerScenario #["escrow-deposit", "escrow-accept", "escrow-refund"] (fun _ => Escrow.cases)
    Escrow.variations Escrow.family ``Escrow.family]

def scenarioFor (mode : String) : Option Scenario :=
  scenarios.find? (fun scenario => scenario.modes.contains mode)

def isContextMode (mode : String) : Bool := (scenarioFor mode).isSome

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
    unless c.scripts.size == 2 do throw "expected two script paths"
    unless ["integer", "data", "data3"].contains c.inputs || isContextMode c.inputs do throw s!"unsupported input mode: {c.inputs}"
    if let some index := c.caseIndex then
      unless isContextMode c.inputs do throw "--case requires a contract input mode"
      unless index < caseCount c.inputs do throw "--case is outside the selected mode's case range"
    for variation in Context.variationNames c.variation do
      unless (variationChoices c.inputs).any (fun entry => entry.1 == variation) do
        throw s!"unsupported variation for {c.inputs}: {variation}"
    unless ["PlutusV1", "PlutusV2", "PlutusV3"].contains c.language do
      throw s!"unsupported language: {c.language}"
    for f in [c.format, c.leftFormat.getD c.format, c.rightFormat.getD c.format] do
      unless formats.contains f do throw s!"unsupported format: {f}"
    return c
  | "--json" :: rest => parse { c with json := true } rest
  | "--worker" :: rest => parse { c with worker := true, json := true } rest
  | "--format" :: v :: rest => parse { c with format := v } rest
  | "--format-left" :: v :: rest => parse { c with leftFormat := some v } rest
  | "--format-right" :: v :: rest => parse { c with rightFormat := some v } rest
  | "--language" :: v :: rest => parse { c with language := v } rest
  | "--inputs" :: v :: rest => parse { c with inputs := v } rest
  | "--case" :: v :: rest => do parse { c with caseIndex := some (← natOption "--case" v) } rest
  | "--variation" :: v :: rest => parse { c with variation := v } rest
  | "--emit-lean" :: v :: rest => parse { c with emitLean := some v } rest
  | "--max-steps" :: v :: rest => do parse { c with steps := ← natOption "--max-steps" v } rest
  | "--left-steps" :: v :: rest => do parse { c with leftSteps := some (← natOption "--left-steps" v) } rest
  | "--right-steps" :: v :: rest => do parse { c with rightSteps := some (← natOption "--right-steps" v) } rest
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
    Side indices select the left (0) or right (1) program and its fuel. -/
structure Query where
  name : String
  declaration : Name
  sides : Array Nat

def queries (c : Config) : Array Query :=
  if isContextMode c.inputs then #[
    ⟨"no_completed_mismatch", ``Context.familyNoCompletedMismatch, #[0, 1]⟩,
    ⟨"total_equivalence", ``Context.familyTotalEquivalence, #[0, 1]⟩,
    ⟨"left_sometimes_output", ``Context.familySometimesOutput, #[0]⟩,
    ⟨"right_sometimes_output", ``Context.familySometimesOutput, #[1]⟩]
  else if c.inputs == "data" then #[
    ⟨"no_completed_mismatch", ``Queries.contextNoCompletedMismatch, #[0, 1]⟩,
    ⟨"total_equivalence", ``Queries.contextTotalEquivalence, #[0, 1]⟩,
    ⟨"left_sometimes_output", ``Queries.contextSometimesOutput, #[0]⟩,
    ⟨"right_sometimes_output", ``Queries.contextSometimesOutput, #[1]⟩]
  else if c.inputs == "data3" then #[
    ⟨"no_completed_mismatch", ``Queries.validatorNoCompletedMismatch, #[0, 1]⟩,
    ⟨"total_equivalence", ``Queries.validatorTotalEquivalence, #[0, 1]⟩,
    ⟨"left_sometimes_output", ``Queries.validatorSometimesOutput, #[0]⟩,
    ⟨"right_sometimes_output", ``Queries.validatorSometimesOutput, #[1]⟩] else #[
    ⟨"shared_integer_outputs", ``Queries.sharedIntegerOutputs, #[0, 1]⟩,
    ⟨"no_completed_mismatch", ``Queries.noCompletedMismatch, #[0, 1]⟩,
    ⟨"total_equivalence", ``Queries.totalEquivalence, #[0, 1]⟩,
    ⟨"left_sometimes_output", ``Queries.sometimesOutput, #[0]⟩,
    ⟨"right_sometimes_output", ``Queries.sometimesOutput, #[1]⟩]

def queryNames (c : Config) : Array String := (queries c).map Query.name

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
  else if isEscrowMode c.inputs then
    let selected := match c.caseIndex, (escrowCases c)[0]? with
      | some index, some choice =>
        s!"; restricted to case {index}: time offset {choice.time.value - 100}, signed={choice.signed}, amount delta={choice.amountDelta}, hasTreasury={choice.hasTreasury}, hasDonation={choice.hasDonation}"
      | _, _ => ""
    s!"CAPE two-party escrow {c.inputs}: price 75000000 lovelace; deposit time 1000000, deadline 2800000; amount price-1/price/price+1; one own escrow input and one output; fixed keys, ASCII script hash, references and Deposited datum; raw integer redeemer; no signer or required signer first with arbitrary Data tail; Deposit upper endpoint 1000000/1000001/1000002 (exclusive), arbitrary lower endpoint; Accept/Refund lower endpoint 2799999/2800000/2800001, arbitrary upper endpoint" ++ selected
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
  let base := if !isHtlcMode c.inputs then baseInputDomain c else
    match c.caseIndex, (htlcCases c)[0]? with
    | some index, some choice =>
      baseInputDomain c ++ s!"; restricted to case {index}: boundary timestamp {choice.time.value}, signed={choice.signed}, doubleInput={choice.doubleInput}, hasTreasury={choice.hasTreasury}, hasDonation={choice.hasDonation}"
    | _, _ => baseInputDomain c
  let base := if isContextMode c.inputs then
    base ++ "; shared list/map/bytestring/integer outer encodings; nonnegative fee and treasury/donation amounts; " ++
      "unbounded unused list/map contents and signature tail; no ledger-validity restriction on nested Data or transaction relationships"
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
def selectedFamilies (c : Config) : Array (Context.Family × Expr) :=
  match scenarioFor c.inputs with
  | some scenario =>
    let families := scenario.families c.inputs (Context.variationNames c.variation)
    match c.caseIndex with
    | some index => families[index]?.toArray
    | none => families
  | none => #[]

def contextFamilies (c : Config) : Array Context.Family := (selectedFamilies c).map Prod.fst

def contextFamilyExprs (c : Config) : Array Expr := (selectedFamilies c).map Prod.snd

def queryPropositions (c : Config) (query : Query) (programs fuels : Array Expr)
    (families : Array Expr := contextFamilyExprs c) : Array Expr :=
  let arguments := query.sides.map (programs[·]!) ++ query.sides.map (fuels[·]!)
  if families.isEmpty then #[mkAppN (mkConst query.declaration) arguments]
  else families.map fun family => mkAppN (mkConst query.declaration) (#[family] ++ arguments)

/-- Conjunction for equivalence/mismatch checks; disjunction for existence of a
    successful execution. Unknown cases cannot establish a universal result. -/
def combineResults (existential : Bool) (left right : Blaster.Smt.Result) : Blaster.Smt.Result :=
  match existential, left, right with
  | true, .Valid, _ | true, _, .Valid => .Valid
  | true, .Falsified _, .Falsified _ => .Falsified []
  | false, .Falsified model, _ | false, _, .Falsified model => .Falsified model
  | false, .Valid, .Valid => .Valid
  | _, _, _ => .Undetermined

/-- Erase fixture/catalog plumbing before Blaster sees the family. Execution
    itself is left to Blaster; only the context-building function is reduced. -/
def prepareContextFamilies (env : Environment) (c : Config) : IO (Array Expr) := do
  let action : MetaM (Array Expr) :=
    (contextFamilyExprs c).mapM (fun family => Meta.reduce family (explicitOnly := false))
  let (families, _) ← action.run' |>.toIO
    { fileName := "<uplc_equiv>", fileMap := default, maxRecDepth := 0, maxHeartbeats := 0 } { env }
  return families

/-- Call Blaster in-process on propositions constructed from decoded programs.
    Results are consumed as an inductive type, without parsing diagnostic text. -/
def solve (env : Environment) (c : Config) (left right : PlutusCore.UPLC.Term.Program)
    (caseResults : Option (IO.Ref (Array (Array Blaster.Smt.Result))) := none)
    (preparedFamilies : Option (Array Expr) := none) : IO (Array Blaster.Smt.Result) := do
  let families ← match preparedFamilies with
    | some families => pure families
    | none => prepareContextFamilies env c
  let programs := #[toExpr left, toExpr right]
  let fuels := #[mkNatLit (c.leftSteps.getD c.steps), mkNatLit (c.rightSteps.getD c.steps)]
  let action : MetaM (Array Blaster.Smt.Result) := do
    let mut results := #[]
    for query in queries c do
      let existential := query.name.endsWith "sometimes_output"
      let mut checked := #[]
      let mut combined : Blaster.Smt.Result := if existential then .Falsified [] else .Valid
      for proposition in queryPropositions c query programs fuels families do
        let solverEnv := { (default : Blaster.Optimize.TranslateEnv) with
          optEnv.options.solverOptions.timeout := some c.timeout
          optEnv.options.solverOptions.generateCex := query.name == "no_completed_mismatch" }
        let ((result, _), _) ← Blaster.Smt.Translate.main proposition |>.run solverEnv
        checked := checked.push result
        combined := combineResults existential combined result
        match existential, combined with
        | true, .Valid | false, .Falsified _ => break
        | _, _ => pure ()
      if let some ref := caseResults then ref.modify (·.push checked)
      results := results.push combined
    return results
  let (results, _) ← action.run' |>.toIO
    { fileName := "<uplc_equiv>", fileMap := default, maxRecDepth := 0, maxHeartbeats := 0 }
    { env }
  return results

def report (verdict explanation : String) (fields : List (String × Json) := []) : Json :=
  Json.mkObj ([("verdict", toJson verdict), ("explanation", toJson explanation)] ++ fields)

/-- Blaster returns model values as strings, e.g. `n: (- 42)\n`.
    Callers with multiple integer parameters also match their binder names. -/
def modelInteger (binding : String) : Option Int :=
  (Model.integerBinding binding).map Prod.snd

def outcomeJson : PlutusCore.UPLC.CekMachine.State → Json
  | .Halt (.VCon (.Integer n)) => Json.mkObj [("kind", toJson "integer"), ("value", toJson n)]
  | .Halt (.VCon .Unit) => Json.mkObj [("kind", toJson "unit")]
  | .Halt value => Json.mkObj [("kind", toJson "non_integer"), ("value", toJson (reprStr value))]
  | .Error => Json.mkObj [("kind", toJson "error")]
  | _ => Json.mkObj [("kind", toJson "unfinished")]

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

/-- A solver witness is only advertised as replayed after native CEK execution
    reproduces a completed mismatch with the original, independent fuel limits. -/
def replayCounterexample (c : Config) (left right : PlutusCore.UPLC.Term.Program)
    (model : List String) : Json := Id.run do
  let replay := fun args input values => do
    let l := execute left args (c.leftSteps.getD c.steps)
    let r := execute right args (c.rightSteps.getD c.steps)
    if compareRuns values l r == .inequivalent then
      some (Json.mkObj [("input", input), ("left", outcomeJson l),
        ("right", outcomeJson r), ("replayed", toJson true)])
    else none
  -- Optimization can reduce a universally false query to False without asking
  -- Z3 for a model. Try zero inputs too, but still require a successful replay.
  let families := contextFamilies c
  if !families.isEmpty then
    let lists := model.filterMap Model.listBinding
    let inputs := (lists.lookup "inputs").getD []
    let outputs := (lists.lookup "outputs").getD []
    let signatureTail := (lists.lookup "signatureTail").getD []
    let timestamps := ((model.filterMap Model.integerBinding).lookup "timestamp").toList ++ [0]
    for unused in [modelContextUnusedTxInfo model, {}] do
      if unused.fee < 0 || unused.treasury < 0 || unused.donation < 0 then continue
      for timestamp in timestamps do
        for family in families do
          let args := family unused inputs outputs signatureTail timestamp
          if let [.Const (.Data context)] := args then
            if let some witness := replay args (Model.dataJson context) (fun _ _ => true) then
              return witness
  else if c.inputs == "data" then
    let candidates := (model.filterMap Model.dataBinding).map Prod.snd ++ [.I 0]
    for context in candidates do
      if let some witness := replay (Queries.contextArgs context) (Model.dataJson context) (fun _ _ => true) then
        return witness
  else if c.inputs == "data3" then
    let bindings := model.filterMap Model.dataBinding
    let find := fun name => (bindings.find? (fun (key, _) => key == name)).map Prod.snd
    let zero := PlutusCore.Data.Data.I 0
    let candidates := [((find "datum").getD zero, (find "redeemer").getD zero, (find "context").getD zero),
      (zero, zero, zero)]
    for (datum, redeemer, context) in candidates do
      let input := Json.mkObj [("datum", Model.dataJson datum),
        ("redeemer", Model.dataJson redeemer), ("context", Model.dataJson context)]
      if let some witness := replay (Queries.dataArgs datum redeemer context) input (fun _ _ => true) then
        return witness
  else
    let candidates := model.filterMap modelInteger ++ [0]
    for n in candidates do
      if let some witness := replay (Queries.args n) (toJson n) integerValues then
        return witness
  let kind := if c.inputs == "integer" then "an integer" else "a Data"
  return Json.mkObj [("replayed", toJson false), ("model", toJson (model.map String.trim)),
    ("reason", toJson s!"Could not extract and replay {kind} witness from Blaster's model.")]

def classify (c : Config) (results : Array Blaster.Smt.Result)
    (left right : PlutusCore.UPLC.Term.Program) : Json := Id.run do
  let mismatch := results[(queryNames c).idxOf "no_completed_mismatch"]?.getD .Undetermined
  let total := results[(queryNames c).idxOf "total_equivalence"]?.getD .Undetermined
  let (verdict, explanation) :=
    if let .Falsified _ := mismatch then
      ("inequivalent", "A common input produces completed, inequivalent outcomes.")
    else if let .Valid := total then
      ("equivalent", "Every input in the declared domain terminates on both sides with equivalent outcomes.")
    else ("inconclusive", "Full equivalence is unestablished: fuel or symbolic reasoning may be insufficient. Agreement between completed runs does not establish termination or full equivalence.")
  let counterexample := match mismatch with
    | .Falsified model => [("counterexample", replayCounterexample c left right model)]
    | _ => []
  return report verdict explanation ([
    ("input_domain", toJson (inputDomain c)),
    ("output_relation", toJson (if c.inputs == "integer" then "integer equality or matching errors" else "acceptance/rejection")),
    ("left_steps", toJson (c.leftSteps.getD c.steps)), ("right_steps", toJson (c.rightSteps.getD c.steps)),
    ("queries", Json.mkObj ((queryNames c).toList.zip (results.toList.map (toJson ∘ status)))),
    ("verification", toJson "Blaster SMT result; no reconstructed Lean proof term")] ++ counterexample)

def emitSource (env : Environment) (c : Config) (caseResults : Array (Array Blaster.Smt.Result) := #[])
    (families : Array Expr := contextFamilyExprs c) : IO Unit := do
  let some file := c.emitLean | return
  let left ← IO.FS.realPath c.scripts[0]!
  let right ← IO.FS.realPath c.scripts[1]!
  let header := s!"import Equivalence.Queries\nimport Equivalence.HTLC\nimport Equivalence.Vesting\nimport Equivalence.Escrow\nimport Blaster\nopen Equivalence.Queries\n#import_uplc left {c.language} {c.leftFormat.getD c.format} {toJson left.toString |>.compress}\n#import_uplc right {c.language} {c.rightFormat.getD c.format} {toJson right.toString |>.compress}\n"
  let project := fun name => mkApp (mkConst ``PlutusCore.UPLC.PlutusScript.PlutusScript.script) (mkConst name)
  let programs := #[project `left, project `right]
  let fuels := #[mkRawNatLit (c.leftSteps.getD c.steps), mkRawNatLit (c.rightSteps.getD c.steps)]
  let chunks ← (queries c).toList.zipIdx.flatMapM fun (query, i) =>
    (queryPropositions c query programs fuels families).toList.zipIdx.filterMapM fun (proposition, j) => do
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
      return some s!"\n-- {query.name}, case {j + 1}\n#blaster (timeout: {c.timeout}){expected} (gen-cex: {if query.name == "no_completed_mismatch" then 1 else 0}) [{rendered.pretty}]\n"
  IO.FS.writeFile file (header ++ String.join chunks)

def run (c : Config) : IO Json := do
  let c ← IO.ofExcept (parse c [])
  let left ← readProgram c.scripts[0]! (c.leftFormat.getD c.format)
  let right ← readProgram c.scripts[1]! (c.rightFormat.getD c.format)
  -- Keep working when the binary is invoked outside the repository or without `lake env`.
  let root := (← IO.appDir) / ".." / ".." / ".."
  initSearchPath toolchainRoot [root / ".lake/build/lib/lean",
    root / ".lake/packages/PlutusCore/.lake/build/lib/lean",
    root / ".lake/packages/Blaster/.lake/build/lib/lean"]
  let env ← importModules #[{ module := `Equivalence.Queries }, { module := `Equivalence.HTLC }, { module := `Equivalence.Vesting }, { module := `Equivalence.Escrow }, { module := `Blaster }] {} (loadExts := true)
  let families ← prepareContextFamilies env c
  emitSource env c #[] families
  let caseResults ← IO.mkRef #[]
  let results ← solve env c left right (some caseResults) (some families)
  emitSource env c (← caseResults.get) families
  return classify c results left right

partial def waitUntil (child : IO.Process.Child cfg) (deadline : Nat) : IO Bool := do
  if (← child.tryWait).isSome then return true
  if (← IO.monoMsNow) ≥ deadline then
    child.kill
    discard child.wait
    return false
  IO.sleep 50
  waitUntil child deadline

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
  let errors ← IO.asTask child.stderr.readToEnd
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
  | some "equivalent" => 0
  | some "inequivalent" => 1
  | some "inconclusive" => 2
  | _ => 3

def printReport (json : Bool) (r : Json) : IO Unit := do
  if json then IO.println r.pretty
  else
    IO.println s!"{(r.getObjValAs? String "verdict").toOption.getD "error"}: {(r.getObjValAs? String "explanation").toOption.getD ""}"
    if let .ok domain := r.getObjValAs? String "input_domain" then
      IO.println s!"Input domain: {domain}"
    if let .ok queries := r.getObjVal? "queries" then
      for name in #["shared_integer_outputs", "no_completed_mismatch", "total_equivalence", "left_sometimes_output", "right_sometimes_output"] do
        if let .ok value := queries.getObjValAs? String name then IO.println s!"  {name}: {value}"
      IO.println "Blaster SMT result; no reconstructed Lean proof term"
    if let .ok witness := r.getObjVal? "counterexample" then
      IO.println s!"Counterexample:\n{witness.pretty}"

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
