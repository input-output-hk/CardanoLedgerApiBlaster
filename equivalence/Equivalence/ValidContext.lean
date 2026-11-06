import Equivalence.Context

/-!
Defines the structured V3 spending-context domain and its configurable count limits.
Generates structured raw context encodings and concrete domain witnesses.
The checker guards validator propositions with the ledger-validity predicate.
Provides smaller acceptance-witness search subsets and syntax for standalone Lean exports.
-/

namespace Equivalence.ValidContext
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.UPLC.Term (Program Term)

/-- Bounds for the structured spending domain. Every length from zero through
    the maximum is included; integer and byte-string contents are unbounded. -/
structure Limits where
  maxInputs : Nat := 2
  maxOutputs : Nat := 2
  maxSigners : Nat := 2
  deriving Repr

/-- Fixed TxInInfo/TxOut encodings with independent symbolic contents.
    Both credential kinds and all three output-datum forms are represented. -/
structure Input where
  txId : ByteString := ⟨String.mk (List.replicate 32 'r')⟩
  index : Int := 0
  isScript : Bool := true
  addressHash : ByteString := ⟨String.mk (List.replicate 28 's')⟩
  ada : Int := 10000000
  policy : ByteString := ⟨String.mk (List.replicate 28 'a')⟩
  token : ByteString := "asset"
  quantity : Int := 1
  hasDatum : Bool := true
  inlineDatum : Bool := true
  datumHash : ByteString := ⟨String.mk (List.replicate 32 'd')⟩
  datum : Data := .I 0

def Input.toData (input : Input) : Data :=
  let address := Data.Constr 0 [
    .Constr (if input.isScript then 1 else 0) [.B input.addressHash], .Constr 1 []]
  let value := context_value% input.ada input.policy input.token input.quantity
  let datum := if input.hasDatum then
    if input.inlineDatum then Data.Constr 2 [input.datum]
    else .Constr 1 [.B input.datumHash]
    else .Constr 0 []
  Context.txInput (Context.outputReference input.txId input.index)
    (.Constr 0 [address, value, datum, .Constr 1 []])

/-- Inverse of the structured input encoding; ledger relationships are separate. -/
def Input.fromData : Data → Option Input
  | .Constr 0 [.Constr 0 [.B txId, .I index], .Constr 0 [
      .Constr 0 [.Constr credential [.B addressHash], .Constr 1 []],
      .Map [(.B "", .Map [(.B "", .I ada)]), (.B policy, .Map [(.B token, .I quantity)])],
      datum, .Constr 1 []]] => do
    unless credential == 0 || credential == 1 do none
    let (hasDatum, inlineDatum, datumHash, payload) ← match datum with
      | .Constr 0 [] => some (false, false, ("" : ByteString), Data.I 0)
      | .Constr 1 [.B hash] => some (true, false, hash, Data.I 0)
      | .Constr 2 [payload] => some (true, true, ("" : ByteString), payload)
      | _ => none
    return {
      txId := txId, index := index, isScript := credential == 1
      addressHash := addressHash, ada := ada, policy := policy, token := token
      quantity := quantity, hasDatum := hasDatum, inlineDatum := inlineDatum
      datumHash := datumHash, datum := payload }
  | _ => none


structure Output where
  address : Data := Context.pubKeyAddress ⟨String.mk (List.replicate 28 'p')⟩
  ada : Int := 9999999
  policy : ByteString := ⟨String.mk (List.replicate 28 'a')⟩
  token : ByteString := "asset"
  quantity : Int := 1
  datum : Data := .I 0

def Output.toData (output : Output) : Data :=
  Context.txOutput output.address
    (context_value% output.ada output.policy output.token output.quantity) (some output.datum)

def Output.fromData : Data → Option Output
  | .Constr 0 [address,
      .Map [(.B "", .Map [(.B "", .I ada)]), (.B policy, .Map [(.B token, .I quantity)])],
      .Constr 2 [datum], .Constr 1 []] =>
    some {
      address := address, ada := ada, policy := policy, token := token,
      quantity := quantity, datum := datum }
  | _ => none

structure Fields where
  scriptTxId : ByteString := ⟨String.mk (List.replicate 32 'r')⟩
  scriptIndex : Int := 0
  datum : Data := .I 0
  redeemer : Data := .Constr 0 []
  validRange : Data := Context.range 0 3000000
  unused : Context.RawUnusedTxInfo := { fee := .I 1 }

def args (f : Fields) (inputs : List Input) (outputs : List Output) (signers : List Data) : List Term :=
  let tx := context_tx_info% f.unused (inputs.map Input.toData)
    (.List (outputs.map Output.toData)) signers f.validRange
  Queries.contextArgs (Context.spendingContext tx f.redeemer
    (Context.outputReference f.scriptTxId f.scriptIndex) f.datum)

def context (f : Fields := {}) (inputs : List Input := [{}])
    (outputs : List Output := [{}]) (signers : List Data := []) : Data :=
  match args f inputs outputs signers with
  | [.Const (.Data raw)] => raw
  | _ => .I 0

def unpack (limits : Limits) (raw : Data) : Option (Fields × List Input × List Output × List Data) := do
  let frame ← Context.unpackSpendingContext raw
  let .Constr 0 [.B scriptTxId, .I scriptIndex] := frame.reference | none
  unless frame.inputs.length ≤ limits.maxInputs && frame.outputs.length ≤ limits.maxOutputs &&
      frame.signers.length ≤ limits.maxSigners &&
      frame.signers.all (fun d => match d with | .B _ => true | _ => false) do none
  let inputs ← frame.inputs.mapM Input.fromData
  let outputs ← frame.outputs.mapM Output.fromData
  return ({
    scriptTxId := scriptTxId, scriptIndex := scriptIndex, datum := frame.datum
    redeemer := frame.redeemer, validRange := frame.validRange, unused := frame.unused },
    inputs, outputs, frame.signers)

def contains (limits : Limits) (raw : Data) : Bool := (unpack limits raw).isSome

/-- A ledger-model-valid zero-output member burns the input's token and pays
    its ADA as the fee. This is a model witness, not an on-chain reachability claim. -/
def validContext (limits : Limits) : Option Data :=
  if limits.maxInputs == 0 then none
  else if limits.maxOutputs > 0 then some (context)
  else
    let input : Input := {}
    some (context { unused := {
      fee := .I input.ada, mint := .Map [(.B input.policy, .Map [(.B input.token, .I (-input.quantity))])] } }
      [input] [])

-- Bounds below guide conservative witness searches only; they do not restrict
-- the declared symbolic domain.
mutual
  /-- All nested integer leaves and constructor tags fit signed 64 bits;
      byte strings have at most 64 bytes. Collection sizes remain unrestricted. -/
  def payload64 : Data → Bool
    | .I n => decide (-(2^63) ≤ n ∧ n < 2^63)
    | .B bytes => bytes.data.length ≤ 64
    | .Constr tag fields => decide (-(2^63) ≤ tag ∧ tag < 2^63) && payloadList64 fields
    | .List fields => payloadList64 fields
    | .Map entries => payloadMap64 entries
  def payloadList64 : List Data → Bool
    | [] => true
    | d :: ds => payload64 d && payloadList64 ds
  def payloadMap64 : List (Data × Data) → Bool
    | [] => true
    | (k, v) :: rest => payload64 k && payload64 v && payloadMap64 rest
end


def witnessPayload (datum redeemer : Data) : Prop := payload64 datum && payload64 redeemer = true

def witnessBytes (bytes : ByteString) : Prop := bytes.data.length ≤ 64

def witnessAmount (ada : Int) : Prop := 0 < ada

def witnessOutputs (count : Nat) (ada : Int) : Prop := Int.ofNat count < ada

/-- A small, inexpensive search subset, independent of contract datum encodings. -/
def fastWitnessRejected (old : Program) (cpu memory : Nat) (v3 : Bool)
    (bounded budgeted : Bool) (steps : Nat) : Prop :=
  ∀ (datum redeemer : Data) (first : ByteString),
    witnessPayload datum redeemer → first.data.length = 28 →
    let inputs := args { datum := datum, redeemer := redeemer }
      [{ datum := datum }] [{ datum := datum }] [.B first]
    Ledger.validArguments inputs →
      Queries.rejected inputs old cpu memory v3 bounded budgeted steps

end Equivalence.ValidContext

namespace Equivalence.ValidContext
open Lean Meta
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.UPLC.Term (Program Term)

private def recordExpr (typeName : Name) (fields : Array Expr) : Expr :=
  mkAppN (mkConst (Name.str typeName "mk")) fields

private def fieldName (stem : String) (field : Name) : Name :=
  Name.mkSimple (if stem.isEmpty then field.toString else stem ++ field.toString.capitalize)

/-- Reflect the record fields so generated binders and constructor arguments
    follow the same order and types as the concrete encoder. -/
private def schema (typeName : Name) (stem := "") : MetaM (Array (Name × Expr)) := do
  let ctor ← getConstInfoCtor (Name.str typeName "mk")
  forallTelescope ctor.type fun fields _ => fields.mapM fun field => do
    let decl ← field.fvarId!.getDecl
    return (fieldName stem decl.userName, decl.type)

private partial def withVariables (specs : List (Name × Expr))
    (k : Array Expr → MetaM Expr) (vars : Array Expr := #[]) : MetaM Expr :=
  match specs with
  | [] => do mkForallFVars vars (← k vars)
  | (name, type) :: rest =>
    withLocalDeclD name type fun var => withVariables rest k (vars.push var)

private partial def withRecords (specs : List (Name × Expr × Expr))
    (k : Array Expr → MetaM Expr) (vars : Array Expr := #[]) : MetaM Expr :=
  match specs with
  | [] => do mkLetFVars vars (← k vars)
  | (name, type, value) :: rest =>
    withLetDecl name type value fun var => withRecords rest k (vars.push var)

private def rawExpr (f : Context.RawUnusedTxInfo) (fee mint : Expr) : Expr :=
  recordExpr ``Context.RawUnusedTxInfo #[
    toExpr f.referenceInputs, toExpr f.outputs, fee, mint,
    toExpr f.certificates, toExpr f.withdrawals, toExpr f.redeemers,
    toExpr f.datums, toExpr f.txId, toExpr f.votes, toExpr f.proposals,
    toExpr f.treasury, toExpr f.donation]

/-- Generate flat primitive binders and concrete list spines for every count.
    The maxima are used when constructing the proposition, never as symbolic
    list-length conditions inside the proposition. -/
def proposition (limits : Limits) (predicate : Expr) : MetaM Expr := do
  let mut specs := #[]
  let mut inputs := #[]
  let mut outputs := #[]
  for i in [:limits.maxInputs] do
    let fields ← schema ``Input s!"input{i}"
    inputs := inputs.push fields
    specs := specs ++ fields
  for i in [:limits.maxOutputs] do
    let fields ← schema ``Output s!"output{i}"
    outputs := outputs.push fields
    specs := specs ++ fields
  let frameFields := (← schema ``Fields).filter (fun (name, _) => name != `unused)
  specs := specs ++ frameFields
  let rawFields ← schema ``Context.RawUnusedTxInfo
  specs := specs ++ rawFields.filter (fun (name, _) => name != `outputs)
  for i in [:limits.maxSigners] do
    specs := specs.push (Name.mkSimple s!"signer{i}", mkConst ``ByteString)
  let result ← withVariables specs.toList fun vars => do
    let bindings := (specs.map Prod.fst).zip vars
    let find := fun name => (bindings.find? (fun (key, _) => key == name)).get!.2
    let unused := recordExpr ``Context.RawUnusedTxInfo (rawFields.map fun (name, _) =>
      if name == `outputs then toExpr (Data.List []) else find name)
    let frame := recordExpr ``Fields ((frameFields.map (fun (name, _) => find name)).push unused)
    let mut records := #[]
    for (fields, i) in inputs.zipIdx do
      records := records.push (Name.mkSimple s!"i{i}", mkConst ``Input,
        recordExpr ``Input (fields.map fun (name, _) => find name))
    for (fields, i) in outputs.zipIdx do
      records := records.push (Name.mkSimple s!"o{i}", mkConst ``Output,
        recordExpr ``Output (fields.map fun (name, _) => find name))
    records := records.push (`f, mkConst ``Fields, frame)
    withRecords records.toList fun records => do
      let inputVars := records.extract 0 limits.maxInputs
      let outputVars := records.extract limits.maxInputs (limits.maxInputs + limits.maxOutputs)
      let f := records.back!
      let keys := (Array.range limits.maxSigners).map fun i =>
        mkApp (mkConst ``Data.B) (find (Name.mkSimple s!"signer{i}"))
      let mut cases := []
      for i in [:limits.maxInputs + 1] do
        for o in [:limits.maxOutputs + 1] do
          for s in [:limits.maxSigners + 1] do
            let args := mkAppN (mkConst ``args) #[f,
              (← mkListLit (mkConst ``Input) (inputVars.extract 0 i).toList),
              (← mkListLit (mkConst ``Output) (outputVars.extract 0 o).toList),
              (← mkListLit (mkConst ``Data) (keys.extract 0 s).toList)]
            cases := mkApp predicate args :: cases
      return mkAndN cases.reverse
  check result
  return result

/-- Generate balanced search subsets for all permitted counts. Only a native
    ledger-valid replay of a falsifying model counts as acceptance evidence. -/
def witnessProposition (limits : Limits) (predicate : Expr) : MetaM Expr := do
  let mut specs := #[(`datum, mkConst ``Data), (`redeemer, mkConst ``Data),
    (`input0AddressHash, mkConst ``ByteString)]
  for i in [:limits.maxInputs] do
    specs := specs.push (Name.mkSimple s!"input{i}Ada", mkConst ``Int)
  for o in [:limits.maxOutputs] do
    specs := specs.push (Name.mkSimple s!"output{o}AddressHash", mkConst ``ByteString)
  for s in [:limits.maxSigners] do
    specs := specs.push (Name.mkSimple s!"signer{s}", mkConst ``ByteString)
  let result ← withVariables specs.toList fun vars => do
    let bindings := (specs.map Prod.fst).zip vars
    let find := fun name => (bindings.find? (fun (key, _) => key == name)).get!.2
    let datum := find `datum
    let redeemer := find `redeemer
    let inputAddress := find `input0AddressHash
    let d : Input := {}
    let f : Fields := {}
    let qty := max limits.maxOutputs 1
    let mut inputVars := #[]
    for i in [:limits.maxInputs] do
      inputVars := inputVars.push (recordExpr ``Input #[toExpr d.txId, toExpr (Int.ofNat i),
        toExpr (i == 0), (if i == 0 then inputAddress else toExpr d.addressHash),
        find (Name.mkSimple s!"input{i}Ada"), toExpr d.policy, toExpr d.token,
        toExpr (Int.ofNat (if i == 0 then qty else 1)),
        toExpr (i == 0), toExpr true, toExpr d.datumHash, datum])
    let keys := (Array.range limits.maxSigners).map fun i =>
      mkApp (mkConst ``Data.B) (find (Name.mkSimple s!"signer{i}"))
    let mut cases := []
    for i in [1:limits.maxInputs + 1] do
      let totalAda := (Array.range i).foldl (fun total n =>
        mkApp2 (mkConst ``Int.add) total (find (Name.mkSimple s!"input{n}Ada"))) (toExpr (0 : Int))
      let totalQty := qty + i - 1
      for o in [:limits.maxOutputs + 1] do
        let mint := if o == 0 then
          Data.Map [(.B d.policy, .Map [(.B d.token, .I (-Int.ofNat totalQty))])]
          else .Map []
        let fee := if o == 0 then mkApp (mkConst ``Data.I) totalAda else toExpr (Data.I 1)
        let unused := rawExpr f.unused fee (toExpr mint)
        let frame := recordExpr ``Fields #[toExpr f.scriptTxId, toExpr f.scriptIndex,
          datum, redeemer, toExpr f.validRange, unused]
        let outputVars := (Array.range o).map fun n => recordExpr ``Output #[
          mkApp (mkConst ``Context.pubKeyAddress) (find (Name.mkSimple s!"output{n}AddressHash")),
          (if n == 0 then mkApp2 (mkConst ``Int.sub) totalAda (toExpr (Int.ofNat o)) else toExpr (1 : Int)),
          toExpr d.policy, toExpr d.token,
          toExpr (Int.ofNat (if n == 0 then totalQty - (o - 1) else 1)), datum]
        for s in [:limits.maxSigners + 1] do
          let args := mkAppN (mkConst ``args) #[frame,
            (← mkListLit (mkConst ``Input) (inputVars.extract 0 i).toList),
            (← mkListLit (mkConst ``Output) outputVars.toList),
            (← mkListLit (mkConst ``Data) (keys.extract 0 s).toList)]
          let clause := mkApp predicate args
          let clause ← if o == 0 then pure clause else
            Lean.mkArrow (mkApp2 (mkConst ``witnessOutputs) (toExpr o) totalAda) clause
          cases := clause :: cases
    let mut body := mkAndN cases.reverse
    for (name, type) in specs.reverse do
      let value := find name
      let condition := if type == mkConst ``ByteString then
          some (mkApp (mkConst ``witnessBytes) value)
        else if type == mkConst ``Int then
          some (mkApp (mkConst ``witnessAmount) value)
        else none
      if let some condition := condition then body ← Lean.mkArrow condition body
    body ← Lean.mkArrow (mkApp2 (mkConst ``witnessPayload) datum redeemer) body
    return body
  check result
  return result

/-- Standalone exports use the same generator as the checker. -/
syntax "valid_context% " num num num term:max : term

elab_rules : term
  | `(valid_context% $inputs:num $outputs:num $signers:num $predicate) => do
    let type ← Lean.mkArrow (mkApp (mkConst ``List [.zero]) (mkConst ``PlutusCore.UPLC.Term.Term)) (mkSort .zero)
    let predicate ← Elab.Term.elabTerm predicate (some type)
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    proposition {
      maxInputs := inputs.getNat, maxOutputs := outputs.getNat,
      maxSigners := signers.getNat } (← instantiateMVars predicate)

end Equivalence.ValidContext
