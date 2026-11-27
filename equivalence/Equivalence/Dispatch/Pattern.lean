import Equivalence.ValidContext
import PlutusCore.Smt.Model

/-! Shared Data patterns for datum and redeemer dispatch. Unmatched payloads and
collection tails are symbolic, not sampled. Parameterized patterns guide witness
search; proof partitions use total fact guards over the original context schema. -/

namespace Equivalence.Dispatch
open Lean Meta
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)

inductive Root where | datum | redeemer | context deriving BEq, Repr
inductive Step where | field (n : Nat) | item (n : Nat) | key (n : Nat) | value (n : Nat) deriving BEq, Repr
structure Path where
  root : Root
  steps : List Step := []
  deriving BEq, Repr

def Path.child (p : Path) (step : Step) : Path := { p with steps := p.steps ++ [step] }

inductive Kind where | constr | map | list | integer | bytes deriving BEq, Repr
inductive Sequence where | fields | items | entries deriving BEq, Repr
inductive Fact where
  | kind (p : Path) (k : Kind)
  | tag (p : Path) (n : Int)
  | equal (p : Path) (value : Data)
  | length (p : Path) (s : Sequence) (n : Nat)
  | notEqual (p : Path) (value : Data)
  | notTag (p : Path) (n : Int)
  | need (p : Path) (s : Sequence) (n : Nat)
  deriving BEq, Repr

instance : ToExpr Root where
  toTypeExpr := mkConst ``Root
  toExpr | .datum => mkConst ``Root.datum | .redeemer => mkConst ``Root.redeemer | .context => mkConst ``Root.context

instance : ToExpr Step where
  toTypeExpr := mkConst ``Step
  toExpr
    | .field n => mkApp (mkConst ``Step.field) (toExpr n)
    | .item n => mkApp (mkConst ``Step.item) (toExpr n)
    | .key n => mkApp (mkConst ``Step.key) (toExpr n)
    | .value n => mkApp (mkConst ``Step.value) (toExpr n)

instance : ToExpr Path where
  toTypeExpr := mkConst ``Path
  toExpr p := mkApp2 (mkConst ``Path.mk) (toExpr p.root) (toExpr p.steps)

instance : ToExpr Kind where
  toTypeExpr := mkConst ``Kind
  toExpr
    | .constr => mkConst ``Kind.constr | .map => mkConst ``Kind.map
    | .list => mkConst ``Kind.list | .integer => mkConst ``Kind.integer | .bytes => mkConst ``Kind.bytes

instance : ToExpr Sequence where
  toTypeExpr := mkConst ``Sequence
  toExpr | .fields => mkConst ``Sequence.fields | .items => mkConst ``Sequence.items | .entries => mkConst ``Sequence.entries

instance : ToExpr Fact where
  toTypeExpr := mkConst ``Fact
  toExpr
    | .kind p k => mkApp2 (mkConst ``Fact.kind) (toExpr p) (toExpr k)
    | .tag p n => mkApp2 (mkConst ``Fact.tag) (toExpr p) (toExpr n)
    | .equal p d => mkApp2 (mkConst ``Fact.equal) (toExpr p) (toExpr d)
    | .notTag p n => mkApp2 (mkConst ``Fact.notTag) (toExpr p) (toExpr n)
    | .notEqual p d => mkApp2 (mkConst ``Fact.notEqual) (toExpr p) (toExpr d)
    | .length p t n => mkApp3 (mkConst ``Fact.length) (toExpr p) (toExpr t) (toExpr n)
    | .need p t n => mkApp3 (mkConst ``Fact.need) (toExpr p) (toExpr t) (toExpr n)

def Fact.path : Fact → Path
  | .kind p _ | .tag p _ | .equal p _ | .notTag p _ | .notEqual p _ | .length p _ _ | .need p _ _ => p

private def readStep (step : Step) (d : Data) : Option Data :=
  match step, d with
  | .field n, .Constr _ fields => fields[n]?
  | .item n, .List items => items[n]?
  | .key n, .Map entries => (entries[n]?).map Prod.fst
  | .value n, .Map entries => (entries[n]?).map Prod.snd
  | _, _ => none

def Path.read (p : Path) (datum redeemer : Data) : Option Data :=
  match p.root with
  | .context => none
  | .datum => p.steps.foldlM (fun d step => readStep step d) datum
  | .redeemer => p.steps.foldlM (fun d step => readStep step d) redeemer

private def dataKind : Data → Kind
  | .Constr .. => .constr | .Map .. => .map | .List .. => .list | .I .. => .integer | .B .. => .bytes

private def sequenceLength (s : Sequence) (d : Data) : Option Nat :=
  match s, d with
  | .fields, .Constr _ fields => some fields.length
  | .items, .List items => some items.length
  | .entries, .Map entries => some entries.length
  | _, _ => none

/-- Check a fact after its path has been resolved. -/
def Fact.holdsValue (f : Fact) (d : Data) : Bool :=
  match f with
  | .kind _ k => dataKind d == k
  | .equal _ expected => d == expected
  | .notEqual _ excluded => d != excluded
  | .tag _ n => match d with | .Constr constructorTag _ => constructorTag == n | _ => false
  | .notTag _ n => match d with | .Constr constructorTag _ => constructorTag != n | _ => false
  | .length _ t n => sequenceLength t d == some n
  | .need _ t n => (sequenceLength t d).any (· ≥ n)

/-- Branch assumptions are checked in both symbolic queries and native probes. -/
def Fact.holds (f : Fact) (datum redeemer : Data) : Bool :=
  (f.path.read datum redeemer).any f.holdsValue

def Path.describe (p : Path) : String :=
  (match p.root with | .datum => "datum" | .redeemer => "redeemer" | .context => "context") ++ String.join (p.steps.map fun step =>
    match step with
    | .field n => s!".field[{n}]" | .item n => s!".item[{n}]"
    | .key n => s!".key[{n}]" | .value n => s!".value[{n}]")

def Fact.exclusion? : Fact → Option String
  | .notEqual p d => some s!"{p.describe} ≠ {d}"
  | .notTag p n => some s!"{p.describe}.tag ≠ {n}"
  | _ => none

inductive Pattern where
  | any
  | literal (value : Data)
  | integer
  | bytes
  | constr (tag : Option Int) (fields : List Pattern) (exact : Bool)
  | list (items : List Pattern) (exact : Bool)
  | map (entries : List (Pattern × Pattern)) (exact : Bool)
  deriving Repr, BEq

partial def Pattern.describe : Pattern → String
  | .any => "?Data"
  | .literal d => toString d
  | .integer => "I ?integer"
  | .bytes => "B ?bytes"
  | .constr tag fields exact =>
    "Constr " ++ (tag.map toString).getD "?tag" ++ " [" ++
      String.intercalate ", " (fields.map Pattern.describe ++ if exact then [] else ["..?fields"]) ++ "]"
  | .list items exact => "List [" ++
      String.intercalate ", " (items.map Pattern.describe ++ if exact then [] else ["..?items"]) ++ "]"
  | .map entries exact => "Map [" ++ String.intercalate ", "
      (entries.map (fun (k,v) => s!"({k.describe}, {v.describe})") ++ if exact then [] else ["..?entries"]) ++ "]"

/-- Membership in a search pattern, including arbitrary collection tails. -/
partial def Pattern.matches (p : Pattern) (d : Data) : Bool :=
  match p, d with
  | .any, _ => true
  | .literal a, b => a == b
  | .integer, .I _ | .bytes, .B _ => true
  | .constr tag fields exact, .Constr actual values =>
    (tag.isNone || tag == some actual) && matchesPrefix fields values exact
  | .list items exact, .List values => matchesPrefix items values exact
  | .map entries exact, .Map values =>
    (if exact then entries.length == values.length else entries.length ≤ values.length) &&
    (entries.zip values).all (fun ((k,v),(a,b)) => k.matches a && v.matches b)
  | _, _ => false
where
  matchesPrefix (patterns : List Pattern) (values : List Data) (exact : Bool) : Bool :=
    (if exact then patterns.length == values.length else patterns.length ≤ values.length) &&
    (patterns.zip values).all (fun (p,d) => p.matches d)

private partial def Pattern.fixed? : Pattern → Option Data
  | .literal d => some d
  | .constr (some tag) fields true => return .Constr tag (← fields.mapM Pattern.fixed?)
  | .list items true => return .List (← items.mapM Pattern.fixed?)
  | .map entries true => return .Map (← entries.mapM fun (k,v) => do
      return (← k.fixed?, ← v.fixed?))
  | _ => none

private def Pattern.kind? : Pattern → Option Kind
  | .any => none | .literal d => some (dataKind d)
  | .integer => some .integer | .bytes => some .bytes
  | .constr .. => some .constr | .list .. => some .list | .map .. => some .map

/-- None means the pattern does not determine this path, not that it is absent. -/
private def Pattern.child? (p : Pattern) (step : Step) : Option Pattern :=
  match p, step with
  | .literal d, step => (readStep step d).map Pattern.literal
  | .constr _ fields _, .field n => fields[n]?
  | .list items _, .item n => items[n]?
  | .map entries _, .key n => (entries[n]?).map Prod.fst
  | .map entries _, .value n => (entries[n]?).map Prod.snd
  | _, _ => none

/-- Only return a Boolean when it is implied by every member of the pattern. -/
private def Pattern.factTruth (p : Pattern) (f : Fact) : Option Bool := do
  let p ← f.path.steps.foldlM Pattern.child? p
  if let some d := p.fixed? then return f.holdsValue d
  let length := fun sequence n atLeast => do
    let (kind, count, exact) ← match p with
      | .constr _ fields exact => some (Sequence.fields, fields.length, exact)
      | .list items exact => some (Sequence.items, items.length, exact)
      | .map entries exact => some (Sequence.entries, entries.length, exact)
      | _ => none
    if sequence != kind then some false
    else if atLeast && count ≥ n then some true
    else if exact then some (if atLeast then count ≥ n else count == n)
    else if !atLeast && count > n then some false
    else none
  match f with
  | .kind _ expected => return (← p.kind?) == expected
  | .equal _ expected => if !p.matches expected then some false else none
  | .notEqual _ excluded => if !p.matches excluded then some true else none
  | .tag _ expected | .notTag _ expected =>
    match p with
    | .constr (some tag) _ _ => some (if f matches .tag .. then tag == expected else tag != expected)
    | _ => if p.kind?.isSome && p.kind? != some .constr then some false else none
  | .length _ sequence n => length sequence n false
  | .need _ sequence n => length sequence n true

private def child (name : String) (index : Nat) : String := name ++ "_" ++ toString index

/-- Flat named binders make the same pattern usable for query construction and model decoding. -/
partial def Pattern.binders (p : Pattern) (name : String) : List (Name × Expr) :=
  let binder := fun suffix type => [(Name.mkSimple (name ++ suffix), mkConst type)]
  match p with
  | .any => binder "" ``Data
  | .literal _ => []
  | .integer => binder "" ``Int
  | .bytes => binder "" ``ByteString
  | .constr tag fields exact =>
    (if tag.isNone then binder "_tag" ``Int else []) ++
    fields.zipIdx.flatMap (fun (p,i) => p.binders (child name i)) ++
    (if exact then [] else [(Name.mkSimple (name ++ "_tail"), mkApp (mkConst ``List [.zero]) (mkConst ``Data))])
  | .list items exact =>
    items.zipIdx.flatMap (fun (p,i) => p.binders (child name i)) ++
    (if exact then [] else [(Name.mkSimple (name ++ "_tail"), mkApp (mkConst ``List [.zero]) (mkConst ``Data))])
  | .map entries exact =>
    entries.zipIdx.flatMap (fun ((k,v),i) =>
      k.binders (child name i ++ "_key") ++ v.binders (child name i ++ "_value")) ++
    (if exact then [] else [(Name.mkSimple (name ++ "_tail"),
      mkApp (mkConst ``List [.zero]) (mkApp2 (mkConst ``Prod [.zero,.zero]) (mkConst ``Data) (mkConst ``Data)))])

private def listExpr (type : Expr) (heads : List Expr) (tail : Expr) : Expr :=
  heads.foldr (fun h t => mkApp3 (mkConst ``List.cons [.zero]) type h t) tail

partial def Pattern.expression (p : Pattern) (name : String) (lookup : Name → Expr) : MetaM Expr := do
  let binder := fun suffix => lookup (Name.mkSimple (name ++ suffix))
  let sequence := fun type items exact => do
    let tail := if exact then mkApp (mkConst ``List.nil [.zero]) type else binder "_tail"
    pure (listExpr type items tail)
  match p with
  | .any => return binder ""
  | .literal d => return toExpr d
  | .integer => return mkApp (mkConst ``Data.I) (binder "")
  | .bytes => return mkApp (mkConst ``Data.B) (binder "")
  | .constr tag fields exact =>
    let values ← fields.zipIdx.mapM fun (p,i) => p.expression (child name i) lookup
    return mkApp2 (mkConst ``Data.Constr) (match tag with | some n => toExpr n | none => binder "_tag")
      (← sequence (mkConst ``Data) values exact)
  | .list items exact =>
    let values ← items.zipIdx.mapM fun (p,i) => p.expression (child name i) lookup
    return mkApp (mkConst ``Data.List) (← sequence (mkConst ``Data) values exact)
  | .map entries exact =>
    let type := mkApp2 (mkConst ``Prod [.zero,.zero]) (mkConst ``Data) (mkConst ``Data)
    let values ← entries.zipIdx.mapM fun ((k,v),i) => do
      return mkApp4 (mkConst ``Prod.mk [.zero,.zero]) (mkConst ``Data) (mkConst ``Data)
        (← k.expression (child name i ++ "_key") lookup) (← v.expression (child name i ++ "_value") lookup)
    return mkApp (mkConst ``Data.Map) (← sequence type values exact)

private def binding (model : List String) (name : String) : Option String := do
  let value ← model.find? (·.startsWith (name ++ ": "))
  if let some (_, .atom symbol) := Blaster.Smt.Model.bindingValue value then
    if symbol.startsWith "$" && (symbol.drop 1 |>.toNat?).isSome then none else some value
  else some value

private def decode [Inhabited α] (model : List String) (name : String)
    (parser : String → Option (String × α)) : Option α :=
  match binding model name with
  | none => some default
  | some value => (parser value).map Prod.snd

/-- Missing/eliminated binders use defaults; callers must still validate and replay the full context. -/
partial def Pattern.value (p : Pattern) (name : String) (model : List String) : Option Data := do
  let dataValue := fun name => match binding model name with
    | none => some (Data.I 0)
    | some b => (PlutusCore.Smt.Model.dataBinding b).map Prod.snd
  let tail := fun exact => if exact then some [] else
    decode model (name ++ "_tail") PlutusCore.Smt.Model.listBinding
  match p with
  | .any => dataValue name
  | .literal d => some d
  | .integer => return .I (← decode model name Blaster.Smt.Model.integerBinding)
  | .bytes => return .B (← decode model name PlutusCore.Smt.Model.byteStringBinding)
  | .constr tag fields exact =>
    let tag ← match tag with
      | some n => some n
      | none => decode model (name ++ "_tag") Blaster.Smt.Model.integerBinding
    return .Constr tag ((← fields.zipIdx.mapM (fun (p,i) => p.value (child name i) model)) ++ (← tail exact))
  | .list items exact =>
    return .List ((← items.zipIdx.mapM (fun (p,i) => p.value (child name i) model)) ++ (← tail exact))
  | .map entries exact =>
    let values ← entries.zipIdx.mapM fun ((k,v),i) => do
      return (← k.value (child name i ++ "_key") model, ← v.value (child name i ++ "_value") model)
    let rest ← if exact then some [] else
      decode model (name ++ "_tail") PlutusCore.Smt.Model.mapBinding
    return .Map (values ++ rest)

structure Case where
  datum : Pattern := .any
  redeemer : Pattern := .any
  conditions : List Fact := []
  deriving Repr, BEq

/-- Remove entailed guards and reject known-impossible cases. Canonical guard order
allows equivalent traces from different implementations to share one probe. -/
def Case.normalize (c : Case) : Option Case := do
  let mut conditions := []
  for fact in c.conditions do
    let pattern ← match fact.path.root with
      | .datum => some c.datum | .redeemer => some c.redeemer | .context => none
    match pattern.factTruth fact with
    | some true => pure ()
    | some false => none
    | none => if !conditions.contains fact then conditions := fact :: conditions
  return { c with conditions := conditions.mergeSort (fun a b => reprStr a ≤ reprStr b) }

/-- Split a broad redeemer alternative at a literal seen in either program. -/
def Case.withRedeemer (c : Case) (value : Data) : Option Case := do
  unless c.redeemer.matches value do none
  { c with redeemer := .literal value }.normalize

def Case.exclusions (c : Case) : List String := c.conditions.filterMap Fact.exclusion?

def Case.describe (c : Case) : String :=
  s!"datum={c.datum.describe}; redeemer={c.redeemer.describe}" ++
    (if c.exclusions.isEmpty then "" else "; " ++ String.intercalate "; " c.exclusions)

def Case.proposition (c : Case) (limits : ValidContext.Limits) (predicate : Expr) : MetaM Expr := do
  let specs := c.datum.binders "dispatch_datum" ++ c.redeemer.binders "dispatch_redeemer"
  let rec bind (remaining : List (Name × Expr)) (values : List (Name × Expr)) : MetaM Expr := do
    match remaining with
    | [] =>
      let find := fun name => (values.lookup name).get!
      let datum ← c.datum.expression "dispatch_datum" find
      let redeemer ← c.redeemer.expression "dispatch_redeemer" find
      let goal ← ValidContext.proposition limits predicate
        (fixedDatum := some datum) (fixedRedeemer := some redeemer)
      if c.conditions.isEmpty then return goal
      let assumptions := c.conditions.foldr (fun fact rest =>
        mkApp2 (mkConst ``Bool.and) (mkApp3 (mkConst ``Fact.holds) (toExpr fact) datum redeemer) rest) (toExpr true)
      -- Keep primitive quantifiers in front of the branch premise. Blaster
      -- accepts prenex queries, not a premise followed by more quantifiers.
      forallTelescope goal fun variables body => do
        mkForallFVars variables (← mkArrow (← mkEq assumptions (toExpr true)) body)
    | (name,type) :: rest =>
      withLocalDeclD name type fun value => do
        mkForallFVars #[value] (← bind rest ((name,value) :: values))
  bind specs []

-- Bind concrete pattern values back into the existing strict model decoder.
-- These strings are decoder input, never submitted as SMT commands.
private def smtText (s : String) : String :=
  "\"" ++ String.join (s.data.map fun c =>
    if c == '"' then "\"\"" else if c.toNat < 32 || c.toNat ≥ 127 || c.toNat == 92 then
      "\\u{" ++ String.mk (Nat.toDigits 16 c.toNat) ++ "}" else String.singleton c) ++ "\""

private def smtInt (n : Int) : String := if n < 0 then s!"(- {n.natAbs})" else toString n

partial def modelData : Data → String
  | .I n => s!"(Data.I {smtInt n})"
  | .B b => s!"(Data.B (ByteString.mk {smtText b.data}))"
  | .Constr tag fields => s!"(Data.Constr {smtInt tag} {list fields})"
  | .List items => s!"(Data.List {list items})"
  | .Map pairs => s!"(Data.Map {pairs.foldr (fun (k,v) rest => s!"(List.cons (Prod.mk {modelData k} {modelData v}) {rest})") "List.nil"})"
where
  list (items : List Data) : String := items.foldr (fun d rest => s!"(List.cons {modelData d} {rest})") "List.nil"

def Case.model (c : Case) (model : List String) : Option (List String) := do
  let datum ← c.datum.value "dispatch_datum" model
  let redeemer ← c.redeemer.value "dispatch_redeemer" model
  unless c.conditions.all (·.holds datum redeemer) do none
  let datumBinding := "datum: " ++ modelData datum
  let redeemerBinding := "redeemer: " ++ modelData redeemer
  unless (PlutusCore.Smt.Model.dataBinding datumBinding).map Prod.snd == some datum &&
      (PlutusCore.Smt.Model.dataBinding redeemerBinding).map Prod.snd == some redeemer do none
  return [datumBinding, redeemerBinding] ++
    model.filter (fun b => !b.startsWith "datum: " && !b.startsWith "redeemer: ")

end Equivalence.Dispatch
