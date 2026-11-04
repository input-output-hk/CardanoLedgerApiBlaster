import Tests.Equivalence.Support

namespace Tests.Equivalence.ValidContext
open Support Lean
open _root_.Equivalence
open PlutusCore.Data (Data)

def settings : Support.Config := {
  bounded := true, steps := 1000, timeout := 15, wallTimeout := 60 }

#eval show IO Unit from do
  let limits : ValidContext.Limits := {}
  unless limits.maxInputs == 2 && limits.maxOutputs == 2 && limits.maxSigners == 2 do
    throw <| IO.userError "Unexpected default maxima"
  let some raw := ValidContext.validContext limits
    | throw <| IO.userError "No default domain witness"
  unless Checker.validLedgerContext settings raw do
    throw <| IO.userError s!"Invalid domain witness: {(Ledger.audit raw).pretty}"
  for isScript in [false, true] do
    for (hasDatum, inlineDatum) in [(false, false), (true, false), (true, true)] do
      let input : ValidContext.Input := {
        isScript := isScript, hasDatum := hasDatum, inlineDatum := inlineDatum
        ada := 2^100, datum := .I (2^100), token := ⟨String.mk (List.replicate 100 'x')⟩ }
      let encoded := input.toData
      unless (ValidContext.Input.fromData encoded).any (fun i => i.toData == encoded) do
        throw <| IO.userError "Structured input failed round-trip"
      let raw := ValidContext.context { validRange := .I 42 } [input]
      let some (f, inputs, outputs, signers) := ValidContext.unpack limits raw
        | throw <| IO.userError "Frame failed to unpack"
      unless ValidContext.context f inputs outputs signers == raw do
        throw <| IO.userError "Frame failed round-trip"
  for maximum in [0, 1, 2, 3] do
    let limits : ValidContext.Limits := { maxInputs := maximum, maxOutputs := maximum, maxSigners := maximum }
    for count in [0, 1, 2, 3, 4] do
      let inputs := List.replicate count ({} : ValidContext.Input)
      let outputs := List.replicate count ({} : ValidContext.Output)
      let signers := List.replicate count (Data.B "")
      unless ValidContext.contains limits (ValidContext.context {} inputs [] []) == (count ≤ maximum) &&
          ValidContext.contains limits (ValidContext.context {} [] outputs []) == (count ≤ maximum) &&
          ValidContext.contains limits (ValidContext.context {} [] [] signers) == (count ≤ maximum) do
        throw <| IO.userError "Replay did not enforce configured maxima"
  unless !Checker.validLedgerContext settings (ValidContext.context {} []) &&
      !ValidContext.contains limits (ValidContext.context {} [{}] [{}] [.I 0]) do
    throw <| IO.userError "Invalid spending frame admitted"
  let zeroOutputs : ValidContext.Limits := { maxOutputs := 0, maxSigners := 0 }
  let some raw := ValidContext.validContext zeroOutputs
    | throw <| IO.userError "No zero-output domain witness"
  unless Checker.validLedgerContext { settings with maxOutputs := 0, maxSigners := 0 } raw do
    throw <| IO.userError s!"Zero-output witness failed: {(Ledger.audit raw).pretty}"
  let limits : ValidContext.Limits := { maxInputs := 3, maxOutputs := 3, maxSigners := 3 }
  let candidates := ValidContext.modelContexts limits ["input0Index: 7", "input2Index: 77",
    "input2IsScript: false", "input2HasDatum: false", "input0Ada: 12345678901234567890",
    "scriptIndex: 7", "validRange: (Data.I 42)", "output2Quantity: 9"]
  unless candidates.any (fun candidate => match ValidContext.unpack limits candidate with
      | some (f, inputs, outputs, _) => f.scriptIndex == 7 && f.validRange == .I 42 &&
          inputs[2]?.any (fun i => i.index == 77 && !i.isScript && !i.hasDatum) &&
          outputs[2]?.any (fun o => o.quantity == 9)
      | none => false) do
    throw <| IO.userError "Lost fields beyond the previous fixed counts"

def branch (condition yes no : String) : String :=
  s!"(force [[[(force (builtin ifThenElse)) {condition}] (delay {yes})] (delay {no})])"

def exactly (count : Nat) (list : String) : String :=
  let empty := s!"[(force (builtin nullList)) {list}]"
  match count with
  | 0 => empty
  | n+1 => branch empty "(con bool False)" (exactly n s!"[(force (builtin tailList)) {list}]")

def transactionList (index : Nat) : String :=
  s!"[(builtin unListData) {contextFieldTerm [0, index]}]"

#eval show IO Unit from do
  let accept := "(lam c (con unit ()))"
  let reject := "(lam c (error))"
  -- Cover each independent maximum, including counts greater than two.
  for (index, options) in [(0, { settings with maxInputs := 3 }),
      (2, { settings with maxOutputs := 3 }), (8, { settings with maxSigners := 3 })] do
    let term := acceptIf (exactly 3 (transactionList index))
    let small ← comparePrograms term accept settings
    verdict small "vacuously_bounded_preserved"
    let large ← comparePrograms term accept options
    verdict large "bounded_preserved"
    expect large ["old_acceptance_status"] "accepted"
    expect large ["old_acceptance_witness", "ledger_validity", "valid"] true
    let regression ← comparePrograms term reject options
    verdict regression "bounded_regression"
    expect (← witness regression) ["ledger_validity", "valid"] true
  let term := acceptIf (exactly 0 (transactionList 0))
  verdict (← comparePrograms term reject settings) "inconclusive"
  -- Zero outputs/signers can form valid members; zero inputs cannot.
  let zero ← comparePrograms accept accept { settings with maxOutputs := 0, maxSigners := 0 }
  verdict zero "bounded_preserved"
  let empty ← comparePrograms accept accept { settings with maxInputs := 0 }
  verdict empty "inconclusive"
  expect empty ["domain_status"] "unestablished"
  let datum := contextFieldTerm [2, 1, 0]
  let condition := branch (exactly 3 (transactionList 0))
    s!"[[(builtin equalsInteger) [(builtin unIData) {datum}]] (con integer 37)]" "(con bool False)"
  let term := acceptIf condition
  let r ← comparePrograms term term { settings with maxInputs := 3, equivalence := true }
  verdict r "bounded_equivalent"
  expect r ["old_acceptance_status"] "accepted"
  expect r ["old_acceptance_witness", "ledger_validity", "valid"] true
  expect (← dataField (← field r ["old_acceptance_witness", "input"]) [2, 1, 0]) ["int"] (37 : Int)

#eval show IO Unit from do
  -- Symbolic funding/recipient search, with two inputs and a 32-byte key.
  let output := s!"[(force (builtin headList)) {transactionList 2}]"
  let firstValue := fun map =>
    s!"[(force (force (builtin sndPair))) [(force (builtin headList)) [(builtin unMapData) {map}]]]"
  let ada := s!"[(builtin unIData) {firstValue (firstValue (dataFieldTerm output [1]))}]"
  let amount := s!"[[(builtin equalsInteger) {ada}] (con integer 75000000)]"
  let recipient := dataFieldTerm output [0, 0, 0]
  let key := String.join (List.replicate 32 "bb")
  let recipientMatches := s!"[[(builtin equalsByteString) [(builtin unBData) {recipient}]] (con bytestring #{key})]"
  let condition := branch (exactly 2 (transactionList 0))
    (branch amount recipientMatches "(con bool False)") "(con bool False)"
  let term := acceptIf condition
  let r ← comparePrograms term term settings
  verdict r "bounded_preserved"
  expect r ["old_acceptance_witness", "ledger_validity", "valid"] true

-- The own input and payment can both be exactly the price; a separate funding
-- input then contributes only the fee. Exercise the search generator directly,
-- so native repair of a primary model cannot hide an over-restricted subset.
#eval show IO Unit from do
  let firstValue := fun map =>
    s!"[(force (force (builtin sndPair))) [(force (builtin headList)) [(builtin unMapData) {map}]]]"
  let own := s!"[(force (builtin headList)) {transactionList 0}]"
  let output := s!"[(force (builtin headList)) {transactionList 2}]"
  let ada := fun value => s!"[(builtin unIData) {firstValue (firstValue value)}]"
  let ownAmount := ada (dataFieldTerm own [1, 1])
  let payment := ada (dataFieldTerm output [1])
  let condition := branch (exactly 2 (transactionList 0))
    (branch (exactly 1 (transactionList 2))
      (branch s!"[[(builtin equalsInteger) {ownAmount}] (con integer 75000000)]"
        s!"[[(builtin equalsInteger) {payment}] (con integer 75000000)]" "(con bool False)")
      "(con bool False)") "(con bool False)"
  let program ← IO.ofExcept (PlutusCore.UPLC.TextEncoding.programFromString
    s!"(program 1.1.0 {acceptIf condition})")
  let options : Checker.Config := {
    bounded := true, steps := 1000, maxInputs := 2, maxOutputs := 1, maxSigners := 0 }
  initSearchPath Checker.toolchainRoot (Checker.moduleSearchPath.map System.FilePath.mk)
  let env ← importModules #[{ module := `Equivalence.ValidContext }, { module := `Blaster }]
    {} (loadExts := true)
  let action : MetaM Blaster.Smt.Result := do
    let predicate ← Checker.queryPredicate options
      { name := "old_rejected", declaration := ``Queries.rejected, sides := #[0] } #[toExpr program]
    let goal ← ValidContext.witnessProposition options.toLimits predicate
    Solver.runQuery goal "fee_only_funding" 15 true
  let (result, _) ← action.run' |>.toIO
    { fileName := "<witness-regression>", fileMap := default, maxRecDepth := 0, maxHeartbeats := 0 } { env }
  let .Falsified bindings := result | throw <| IO.userError "Witness search excluded fee-only funding"
  let replay := Checker.replayOldAcceptance options program program bindings
  expect replay ["replayed"] true
  expect replay ["ledger_validity", "valid"] true

end Tests.Equivalence.ValidContext
