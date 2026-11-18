import Tests.Equivalence.Support
import Equivalence.Dispatch.Discover

namespace Tests.Equivalence.Dispatch
open Lean _root_.Equivalence
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open Support

private def program (term : String) : IO PlutusCore.UPLC.Term.Program :=
  IO.ofExcept (PlutusCore.UPLC.TextEncoding.programFromString s!"(program 1.1.0 {term})")

#eval show IO Unit from do
  -- Neither datum nor redeemer has a privileged Data type.
  let fixtures : List (String × Data) := [
    ("I 7", .I 7), ("B #6869", .B "hi"), ("Constr 3 [I 4]", .Constr 3 [.I 4]),
    ("List [I 1, I 2]", .List [.I 1,.I 2]), ("Map [(I 1, B #61)]", .Map [(.I 1,.B "a")])]
  for datum in [false,true] do
    let source := dataFieldTerm "c" (if datum then [2,1,0] else [1])
    for (literal,value) in fixtures do
      let p ← program <| acceptIf s!"[[(builtin equalsData) {source}] (con data ({literal}))]"
      let found := _root_.Equivalence.Dispatch.discover {} p p
      unless found.cases.any (fun c => (if datum then c.datum else c.redeemer) == .literal value) do
        throw <| IO.userError s!"Missed {literal} on {if datum then "datum" else "redeemer"}: {repr found}"
  -- Integer decoding and UTF-8 string comparisons retain their originating path.
  let redeemer := dataFieldTerm "c" [1]
  for (condition,value) in [
      (s!"[[(builtin equalsInteger) (con integer 9)] [(builtin unIData) {redeemer}]]", Data.I 9),
      (s!"[[(builtin equalsByteString) [(builtin unBData) {redeemer}]] (con bytestring #6869)]", Data.B "hi"),
      (s!"[[(builtin equalsString) [(builtin decodeUtf8) [(builtin unBData) {redeemer}]]] (con string \"hi\")]", Data.B "hi")] do
    let p ← program (acceptIf condition)
    let found := _root_.Equivalence.Dispatch.discover {} p p
    unless found.cases.any (fun c => c.redeemer == .literal value) do
      throw <| IO.userError s!"Missed scalar dispatch: {condition}"
  let tag := s!"[(force (force (builtin fstPair))) [(builtin unConstrData) {redeemer}]]"
  let p ← program <| acceptIf s!"[[(builtin equalsInteger) {tag}] (con integer 5)]"
  let found := _root_.Equivalence.Dispatch.discover {} p p
  unless found.cases.any (fun c => c.redeemer == .constr (some 5) [] false) do
    throw <| IO.userError "Constructor payloads must remain symbolic, including unknown-length fields"
  -- Work limits never invent exhaustiveness.
  let p ← program "(lam c [(lam x [x x]) (lam x [x x])])"
  let found := _root_.Equivalence.Dispatch.discover {} p p
  unless found.limited && found.cases.isEmpty && !found.limitReasons.isEmpty do
    throw <| IO.userError "Unbounded or unexplained discovery"
  let p ← program <| acceptIf s!"[[(builtin equalsInteger) [(builtin unIData) {redeemer}]] (con integer 1)]"
  let q ← program <| acceptIf s!"[[(builtin equalsInteger) [(builtin unIData) {redeemer}]] (con integer 2)]"
  let found := _root_.Equivalence.Dispatch.discover {} p q 1
  unless found.limited && found.cases.size == 1 && found.limitReasons.contains "case limit" do
    throw <| IO.userError "Case limit was not reported"
  -- User-supplied arguments remain restrictions, even when the scripts inspect them.
  let fixed := _root_.Equivalence.Dispatch.discover
    { datum := some (.Constr 4 []), redeemer := some (.I 99) } p q
  unless fixed.cases.isEmpty do throw <| IO.userError "Discovery replaced fixed arguments"

private def branch (condition yes no : String) : String :=
  s!"(force [[[(force (builtin ifThenElse)) {condition}] (delay {yes})] (delay {no})])"

#eval show IO Unit from do
  let datum := dataFieldTerm "c" [2,1,0]
  let redeemer := dataFieldTerm "c" [1]
  let tag := s!"[(force (force (builtin fstPair))) [(builtin unConstrData) {redeemer}]]"
  let fields := s!"[(force (force (builtin sndPair))) [(builtin unConstrData) {redeemer}]]"
  let payload := s!"[(builtin unBData) [(force (builtin headList)) {fields}]]"
  let checkDatum := fun literal => branch s!"[[(builtin equalsData) {datum}] (con data ({literal}))]" "(con unit ())" "(error)"
  let first := s!"[(lam ignored {checkDatum "I 10"}) {payload}]"
  let second := checkDatum "B #62"
  let body := branch s!"[[(builtin equalsInteger) {tag}] (con integer 0)]" first
    (branch s!"[[(builtin equalsInteger) {tag}] (con integer 1)]" second "(error)")
  let p ← program s!"(lam c {body})"
  let found := _root_.Equivalence.Dispatch.discover {} p p
  let hasPair := fun datum redeemer => found.cases.any (fun c => c.datum == datum && c.redeemer == redeemer)
  unless hasPair (.literal (.I 10)) (.constr (some 0) [.bytes] true) do
    throw <| IO.userError s!"Lost payload-bearing branch: {repr found}"
  unless hasPair (.literal (.B "b")) (.constr (some 1) [] true) do
    throw <| IO.userError s!"Payload leaked into the empty branch: {repr found}"
  for c in found.cases do
    if c.datum == .literal (.I 10) then
      unless c.redeemer == .constr (some 0) [.bytes] true || c.redeemer == .constr (some 0) [.bytes] false do
        throw <| IO.userError "Datum from branch 0 crossed into another redeemer"
    if c.datum == .literal (.B "b") then
      unless c.redeemer == .constr (some 1) [] true || c.redeemer == .constr (some 1) [] false do
        throw <| IO.userError "Datum from branch 1 crossed into another redeemer"
  let capped := _root_.Equivalence.Dispatch.discover {} p p 2
  unless capped.cases.any (·.redeemer == .constr (some 0) [.bytes] true) &&
      capped.cases.any (·.redeemer == .constr (some 1) [] true) do
    throw <| IO.userError "Datum variants crowded out another redeemer branch"
  -- One redeemer can select several datum alternatives.
  let datums := branch s!"[[(builtin equalsData) {datum}] (con data (I 10))]" "(con unit ())"
    (branch s!"[[(builtin equalsData) {datum}] (con data (I 20))]" "(con unit ())" "(error)")
  let p ← program s!"(lam c {branch s!"[[(builtin equalsData) {redeemer}] (con data (I 7))]" datums "(error)"})"
  let alternatives := _root_.Equivalence.Dispatch.discover {} p p
  for value in [10,20] do
    unless alternatives.cases.any (fun c => c.redeemer == .literal (.I 7) && c.datum == .literal (.I value)) do
      throw <| IO.userError "Lost a datum alternative for the same redeemer"
  -- Correlation must also survive when the datum is inspected first.
  let rootA := datum
  let rootB := redeemer
  let a := branch s!"[[(builtin equalsData) {rootB}] (con data (I 7))]" "(con unit ())" "(error)"
  let b := branch s!"[[(builtin equalsData) {rootB}] (con data (B #62))]" "(con unit ())" "(error)"
  let p ← program s!"(lam c {branch s!"[[(builtin equalsData) {rootA}] (con data (I 10))]" a b})"
  let found := _root_.Equivalence.Dispatch.discover {} p p
  unless found.cases.any (fun c => c.datum == .literal (.I 10) && c.redeemer == .literal (.I 7)) do
    throw <| IO.userError "Lost datum-first branch"
  unless found.cases.any (fun c => c.redeemer == .literal (.B "b") &&
      c.conditions.contains (.notEqual ⟨.datum,[]⟩ (.I 10))) do
    throw <| IO.userError "Lost datum-first else condition"

#eval show IO Unit from do
  -- Follow the ledger aliases as well as direct ScriptInfo/context fields.
  let inputs := dataFieldTerm "c" [0,0]
  let ownInput := s!"[(force (builtin headList)) [(builtin unListData) {inputs}]]"
  let inlineDatum := dataFieldTerm ownInput [1,2,0]
  let entries := s!"[(builtin unMapData) {dataFieldTerm "c" [0,9]}]"
  let entry := s!"[(force (builtin headList)) {entries}]"
  let redeemer := s!"[(force (force (builtin sndPair))) {entry}]"
  let p ← program <| acceptIf s!"[[(builtin equalsData) {inlineDatum}] (con data (I 10))]"
  let q ← program <| acceptIf s!"[[(builtin equalsData) {redeemer}] (con data (I 7))]"
  let found := _root_.Equivalence.Dispatch.discover {} p q
  unless found.cases.any (·.datum == .literal (.I 10)) &&
      found.cases.any (·.redeemer == .literal (.I 7)) do
    throw <| IO.userError "Lost own-input datum or spending redeemer aliases"
  unless found.cases.all (fun c => c.conditions.all (·.path.root != .context)) do
    throw <| IO.userError "Transaction exploration leaked into dispatch constraints"
  -- An already selected constructor cannot later take a contradictory branch.
  let r := dataFieldTerm "c" [1]
  let tag := s!"[(force (force (builtin fstPair))) [(builtin unConstrData) {r}]]"
  let impossible := branch s!"[[(builtin equalsInteger) {tag}] (con integer 1)]"
    (branch s!"[[(builtin equalsData) {dataFieldTerm "c" [2,1,0]}] (con data (I 999))]" "(con unit ())" "(error)") "(error)"
  let p ← program s!"(lam c {branch s!"[[(builtin equalsInteger) {tag}] (con integer 0)]" impossible "(error)"})"
  let found := _root_.Equivalence.Dispatch.discover {} p p
  unless found.cases.all (·.datum != .literal (.I 999)) do
    throw <| IO.userError "Explored a contradictory selector branch"

#eval show IO Unit from do
  let scalus ← readProgram "equivalence/examples/htlc/Scalus_0.18.2_Unisay.cbor_hex"
  let plinth ← readProgram "equivalence/examples/htlc/Plinth_1.67.0.0_Unisay.cbor_hex"
  let found := _root_.Equivalence.Dispatch.discover {} scalus plinth
  unless found.cases.any (·.redeemer == .constr (some 0) [.bytes] true) &&
      found.cases.any (·.redeemer == .constr (some 1) [] true) do
    throw <| IO.userError "Real HTLC discovery lost distinct payload shapes"

#eval show IO Unit from do
  -- Normalization must preserve the domain, including nested paths, absent
  -- fields, collection tails and every Data kind.
  let values : List Data := [.I (-1), .I 0, .I 1, .I 2, .B "", .B "a",
    .Constr 0 [], .Constr 0 [.I 0], .Constr 1 [], .List [], .List [.I 0],
    .Map [], .Map [(.I 0,.B "a")]]
  let patterns : List _root_.Equivalence.Dispatch.Pattern := [
    .any, .literal (.I 0), .integer, .bytes, .constr none [.any] false,
    .constr (some 1) [] true, .list [.integer] false, .map [(.integer,.bytes)] false]
  let facts : List _root_.Equivalence.Dispatch.Fact := [
    .kind ⟨.datum,[]⟩ .integer, .equal ⟨.datum,[]⟩ (.I 0), .notEqual ⟨.datum,[]⟩ (.I 1),
    .tag ⟨.datum,[]⟩ 0, .notTag ⟨.datum,[]⟩ 1, .length ⟨.datum,[]⟩ .fields 1,
    .need ⟨.datum,[]⟩ .fields 1, .length ⟨.datum,[]⟩ .items 1,
    .need ⟨.datum,[]⟩ .entries 1, .kind ⟨.datum,[.field 0]⟩ .bytes,
    .notEqual ⟨.datum,[.field 0]⟩ (.I 1), .notEqual ⟨.redeemer,[]⟩ (.I 0)]
  let member := fun (c : _root_.Equivalence.Dispatch.Case) datum redeemer =>
    c.datum.matches datum && c.redeemer.matches redeemer && c.conditions.all (·.holds datum redeemer)
  for pattern in patterns do
    for fact in facts do
      let c : _root_.Equivalence.Dispatch.Case := { datum := pattern, conditions := [fact] }
      let normalized := c.normalize
      for datum in values do
        for redeemer in values do
          unless member c datum redeemer == normalized.any (fun c => member c datum redeemer) do
            throw <| IO.userError s!"Normalization changed {repr c} on {datum}, {redeemer}"
  let a : _root_.Equivalence.Dispatch.Case := {
    redeemer := .literal (.I 1)
    conditions := [.kind ⟨.redeemer,[]⟩ .integer, .notEqual ⟨.redeemer,[]⟩ (.I 0)] }
  unless a.normalize == some { redeemer := .literal (.I 1) } do
    throw <| IO.userError "Fixed redeemer retained redundant guards"
  let excludedDatum : _root_.Equivalence.Dispatch.Fact := .notEqual ⟨.datum,[]⟩ (.I 1)
  let excludedRedeemer : _root_.Equivalence.Dispatch.Fact := .notEqual ⟨.redeemer,[]⟩ (.I 0)
  let a : _root_.Equivalence.Dispatch.Case := { conditions := [excludedDatum, excludedRedeemer] }
  let b : _root_.Equivalence.Dispatch.Case := { conditions := [excludedRedeemer, excludedDatum, excludedDatum] }
  unless a.normalize == b.normalize do throw <| IO.userError "Guard order changed case identity"

#eval show IO Unit from do
  -- A compiler's generic else alternative also applies at literal selectors
  -- tested only by the other compiler. Carry its datum requirements there.
  let datum := dataFieldTerm "c" [2,1,0]
  let redeemer := dataFieldTerm "c" [1]
  let checkDatum := fun value => branch s!"[[(builtin equalsData) {datum}] (con data (I {value}))]"
    "(con unit ())" "(error)"
  let make := fun selector yes no => program s!"(lam c {branch s!"[[(builtin equalsData) {redeemer}] (con data (I {selector}))]" (checkDatum yes) (checkDatum no)})"
  let left ← make 0 10 20
  let right ← make 1 30 40
  let found := _root_.Equivalence.Dispatch.discover {} left right
  for (r,d) in [(0,10),(0,40),(1,20),(1,30)] do
    unless found.cases.any (fun c => c.redeemer == .literal (.I r) && c.datum == .literal (.I d) && c.conditions.isEmpty) do
      throw <| IO.userError s!"Lost datum {d} at redeemer {r}: {repr found}"
  for c in found.cases do
    if c.redeemer == .any then
      unless c.conditions.contains (.notEqual ⟨.redeemer,[]⟩ (.I 0)) &&
          c.conditions.contains (.notEqual ⟨.redeemer,[]⟩ (.I 1)) do
        throw <| IO.userError "Residual redeemer still overlaps a named selector"
  unless found.cases.toList.eraseDups.length == found.cases.size do
    throw <| IO.userError "Equivalent compiler traces created duplicate probes"

#eval show IO Unit from do
  -- Model aliases preserve every Data kind, including bytes needing SMT escaping.
  let bytes : ByteString := ⟨String.mk [Char.ofNat 0, '\\', 'u', '{', '4', '1', '}', '"', Char.ofNat 255]⟩
  let values : List Data := [.I (-42), .B bytes, .Constr 3 [.I 9],
    .List [.B bytes, .Constr 0 []], .Map [(.B bytes, .List [.I 7])]]
  for value in values do
    let encoded := "x: " ++ _root_.Equivalence.Dispatch.modelData value
    unless (PlutusCore.Smt.Model.dataBinding encoded).map Prod.snd == some value do
      throw <| IO.userError s!"Data alias failed to round-trip: {encoded}"
    let c : _root_.Equivalence.Dispatch.Case := { datum := .literal value, redeemer := .literal value }
    unless (c.model []).isSome do throw <| IO.userError "Literal Data case failed"
  let c : _root_.Equivalence.Dispatch.Case := {
    datum := .constr (some 0) [.constr (some 0) [] true, .integer] true
    redeemer := .literal (.B "go") }
  let some model := c.model ["dispatch_datum_1: 123456\n"]
    | throw <| IO.userError "Nested pattern model failed"
  let datum := model.filterMap PlutusCore.Smt.Model.dataBinding |>.lookup "datum"
  unless datum == some (.Constr 0 [.Constr 0 [], .I 123456]) do
    throw <| IO.userError "Nested integer payload was not symbolic"
  let guarded : _root_.Equivalence.Dispatch.Case := {
    redeemer := .integer, conditions := [.notEqual ⟨.redeemer,[]⟩ (.I 0)] }
  unless (guarded.model []).isNone && (guarded.model ["dispatch_redeemer: 1"]).isSome do
    throw <| IO.userError "Native model decoding ignored a branch exclusion"

open Lean Elab Command Meta in
run_elab do
  let type ← mkArrow (mkApp (mkConst ``List [.zero])
    (mkConst ``PlutusCore.UPLC.Term.Term)) (mkSort .zero)
  withLocalDeclD `p type fun predicate => do
    let patterns : List _root_.Equivalence.Dispatch.Pattern := [
      .any, .integer, .bytes, .literal (.I 7), .constr none [.integer,.bytes] false,
      .list [.any,.constr (some 3) [] true] false, .map [(.bytes,.integer)] false]
    for pattern in patterns do
      let c : _root_.Equivalence.Dispatch.Case := {
        datum := pattern, redeemer := pattern
        conditions := [.notEqual ⟨.redeemer,[]⟩ (.I 0), .notTag ⟨.datum,[]⟩ 1] }
      let goal ← c.proposition {} predicate
      let closed ← mkForallFVars #[predicate] goal
      check closed
      unless !closed.hasFVar && !closed.hasMVar do throwError "Pattern query is not closed"

end Tests.Equivalence.Dispatch
