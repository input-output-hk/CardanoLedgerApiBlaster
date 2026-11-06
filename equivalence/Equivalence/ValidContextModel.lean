import Equivalence.ValidContext
import PlutusCore.Smt.Model

/-!
Reconstructs structured spending-context candidates from primitive SMT model bindings.
Enumerates count cases and tries sanitized or balanced variants to aid witness replay.
Candidates still require independent domain checks, ledger validation and execution replay.
-/

namespace Equivalence.ValidContext
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)

private def unusedFromModel (data : List (String × Data))
    (defaults : Context.RawUnusedTxInfo) : Context.RawUnusedTxInfo :=
  let raw := fun name value => (data.lookup name).getD value
  { referenceInputs := raw "referenceInputs" defaults.referenceInputs
    fee := raw "fee" defaults.fee, mint := raw "mint" defaults.mint
    certificates := raw "certificates" defaults.certificates
    withdrawals := raw "withdrawals" defaults.withdrawals
    redeemers := raw "redeemers" defaults.redeemers, datums := raw "datums" defaults.datums
    txId := raw "txId" defaults.txId, votes := raw "votes" defaults.votes
    proposals := raw "proposals" defaults.proposals
    treasury := raw "treasury" defaults.treasury, donation := raw "donation" defaults.donation }

/-- Repair only a candidate, never the proof domain. Every returned candidate
    still requires ledger validation and execution replay before it is evidence. -/
private def sanitize (f : Fields) : Fields := Id.run do
  let probe := context
  let .Constr _ [tx, _, _] := probe | return f
  let raw := fun index value fallback =>
    if (Ledger.decode (Context.setField probe 0 (Context.setField tx index value))).isSome
    then value else fallback
  let d : Fields := {}
  let u := f.unused
  let rangeProbe := Context.setField probe 0 (Context.setField tx 7 f.validRange)
  let rangeValid := ((Ledger.checks rangeProbe).lookup "validity_interval").getD false
  return { f with
    validRange := if rangeValid then f.validRange else d.validRange
    unused := {
      referenceInputs := raw 1 u.referenceInputs d.unused.referenceInputs
      fee := raw 3 u.fee d.unused.fee, mint := raw 4 u.mint d.unused.mint
      certificates := raw 5 u.certificates d.unused.certificates
      withdrawals := raw 6 u.withdrawals d.unused.withdrawals
      redeemers := raw 9 u.redeemers d.unused.redeemers
      datums := raw 10 u.datums d.unused.datums, txId := raw 11 u.txId d.unused.txId
      votes := raw 12 u.votes d.unused.votes, proposals := raw 13 u.proposals d.unused.proposals
      treasury := raw 14 u.treasury d.unused.treasury, donation := raw 15 u.donation d.unused.donation } }

private def balance (f : Fields) (inputs : List Input) (outputs : List Output)
    (anchor : Nat) : Fields × List Input := Id.run do
  if inputs.isEmpty then return (f, inputs)
  let totalAda := (inputs.map (·.ada)).sum
  let totalQty := (inputs.map (·.quantity)).sum
  if outputs.isEmpty then
    let d := inputs[0]?.getD ({} : Input)
    return ({ f with unused := { f.unused with
      fee := .I totalAda,
      mint := .Map [(.B d.policy, .Map [(.B d.token, .I (-totalQty))])] } }, inputs)
  let fee := match f.unused.fee with | .I n => n | _ => 1
  let old := inputs[anchor]?.getD ({} : Input)
  let ada := (outputs.map (·.ada)).sum + fee - (totalAda - old.ada)
  let quantity := (outputs.map (·.quantity)).sum - (totalQty - old.quantity)
  return (f, inputs.modify anchor fun input => { input with ada := ada, quantity := quantity })

/-- Models expose individual primitive fields. Enumerate the same count cases
    as the symbolic generator. Invalid or repaired models are never accepted
    without independently validating the full context and reproducing behavior. -/
def modelContexts (limits : Limits) (model : List String) : List Data := Id.run do
  let data := model.filterMap PlutusCore.Smt.Model.dataBinding
  let integers := model.filterMap Blaster.Smt.Model.integerBinding
  let bytes := model.filterMap PlutusCore.Smt.Model.byteStringBinding
  let flags := model.filterMap Blaster.Smt.Model.boolBinding
  let raw := fun name value => (data.lookup name).getD value
  let number := fun name value => (integers.lookup name).getD value
  let key := fun name value => (bytes.lookup name).getD value
  let flag := fun name value => (flags.lookup name).getD value
  let d : Fields := {}
  let f : Fields := {
    scriptTxId := key "scriptTxId" d.scriptTxId, scriptIndex := number "scriptIndex" d.scriptIndex
    datum := raw "datum" d.datum, redeemer := raw "redeemer" d.redeemer
    validRange := raw "validRange" d.validRange, unused := unusedFromModel data d.unused }
  let sanitized := sanitize f
  let input := fun (i : Nat) =>
    let stem := s!"input{i}"
    let d : Input := {
      index := Int.ofNat i, isScript := i == 0, hasDatum := i == 0,
      quantity := if i == 0 then Int.ofNat (max limits.maxOutputs 1) else 1 }
    ({
      txId := key (stem ++ "TxId") d.txId, index := number (stem ++ "Index") d.index
      isScript := flag (stem ++ "IsScript") d.isScript
      addressHash := key (stem ++ "AddressHash") d.addressHash
      ada := number (stem ++ "Ada") d.ada, policy := key (stem ++ "Policy") d.policy
      token := key (stem ++ "Token") d.token, quantity := number (stem ++ "Quantity") d.quantity
      hasDatum := flag (stem ++ "HasDatum") d.hasDatum
      inlineDatum := flag (stem ++ "InlineDatum") d.inlineDatum
      datumHash := key (stem ++ "DatumHash") d.datumHash
      datum := raw (stem ++ "Datum") f.datum } : Input)
  let inputs := (List.range limits.maxInputs).map input
  let fee := match sanitized.unused.fee with | .I n => n | _ => 1
  let keys := (List.range limits.maxSigners).map fun i =>
    let suffix := toString i
    key s!"signer{i}" ⟨String.mk (List.replicate (28 - suffix.length) '0') ++ suffix⟩
  let signerCases := (List.range (limits.maxSigners + 1)).flatMap fun count =>
    let signers := keys.take count
    let sorted := (signers.mergeSort (fun a b => decide (a.data ≤ b.data))).eraseDups
    (if signers == sorted then [signers] else [signers, sorted]).map (·.map Data.B)
  let mut candidates := []
  for inputCount in List.range (limits.maxInputs + 1) do
    let inputs := inputs.take inputCount
    let totalAda := (inputs.map (·.ada)).sum
    let totalQty := (inputs.map (·.quantity)).sum
    let asset := inputs[0]?.getD ({} : Input)
    let inputsAligned := inputs.modify 0 fun input => { input with
      txId := f.scriptTxId, index := f.scriptIndex, isScript := true
      hasDatum := true, inlineDatum := true, datum := f.datum }
    for outputCount in List.range (limits.maxOutputs + 1) do
      let outputs := (List.range outputCount).map fun i =>
        let stem := s!"output{i}"
        let d : Output := {}
        ({
          address := raw (stem ++ "Address") ((bytes.lookup (stem ++ "AddressHash")).map
            Context.pubKeyAddress |>.getD d.address)
          ada := number (stem ++ "Ada") (if i == 0 then totalAda - fee - Int.ofNat (outputCount - 1) else 1)
          policy := key (stem ++ "Policy") asset.policy, token := key (stem ++ "Token") asset.token
          quantity := number (stem ++ "Quantity") (if i == 0 then totalQty - Int.ofNat (outputCount - 1) else 1)
          datum := raw (stem ++ "Datum") f.datum } : Output)
      let outputsSafe := outputs.map fun output =>
        if (Ledger.decode (context {} [{}] [output])).isSome then output
        else { output with address := match output.address with
          | .Constr _ (.Constr 0 [.B key] :: _) => Context.pubKeyAddress key
          | .Constr _ (.Constr 1 [.B hash] :: _) => Context.scriptAddress hash
          | _ => ({} : Output).address }
      let balancedCases := (if inputCount ≤ 1 then [0] else [0, inputCount - 1]).map
        (balance sanitized inputsAligned outputsSafe)
      for signers in signerCases do
        candidates := context f inputs outputs signers :: candidates
        candidates := context sanitized inputs outputsSafe signers :: candidates
        for (f, balanced) in balancedCases do
          candidates := context f balanced outputsSafe signers :: candidates
  return candidates.reverse

end Equivalence.ValidContext
