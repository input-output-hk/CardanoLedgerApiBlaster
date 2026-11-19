import PlutusCore.UPLC.PreProcess
import PlutusCore.UPLC.Utils

/-!
Small schema-directed adapter generator used by AutomaticMapping.lean.

Supported fragment: named integer quantities, exact integer unit expansion,
arbitrary extra Data arguments, and fixed integer arguments. Names are semantic
correspondences supplied by the simulated schemas; units are annotations, not
guessed from executable code. Unsupported or lossy conversions are rejected.
-/
namespace Equivalence.MappingExamples.MappingSupport

open PlutusCore.Data (Data)
open PlutusCore.UPLC.Term (Term Const BuiltinFun)
open PlutusCore.UPLC.PlutusScript (PlutusScript)
open PlutusCore.UPLC.CekMachine (State)

structure Quantity where
  name : String
  unitsPerWhole : Nat := 1
  deriving Repr

inductive TargetField where
  | quantity : Quantity → TargetField
  | extraData : TargetField
  | fixed : Int → TargetField
  deriving Repr

inductive Rule where
  | source (index factor : Nat)
  | extra (index : Nat)
  | fixed (value : Int)
  deriving Repr

structure Mapping where
  sourceCount : Nat
  extraCount : Nat
  rules : List Rule
  deriving Repr

private def findSource (name : String) : List Quantity → Nat → Option (Nat × Quantity)
  | [], _ => none
  | q :: qs, index => if q.name == name then some (index, q) else findSource name qs (index + 1)

private def uniqueNames : List Quantity → Bool
  | [] => true
  | q :: qs => !(qs.any fun other => q.name == other.name) && uniqueNames qs

/-- Infer permutations and scaling from the schemas; retain every source quantity. -/
def inferMapping (source : List Quantity) (target : List TargetField) : Except String Mapping := do
  if !uniqueNames source then throw "Ambiguous source quantity names"
  if source.any (fun q => q.unitsPerWhole == 0) then throw "Source units must be positive"
  let (rules, extras) ← visit target 0
  if !(List.range source.length).all (fun index => rules.any fun
      | .source i _ => i == index
      | _ => false) then
    throw "A source quantity is missing from the target"
  return ⟨source.length, extras, rules⟩
where
  visit : List TargetField → Nat → Except String (List Rule × Nat)
    | [], extra => .ok ([], extra)
    | field :: rest, extra => do
      let (rule, nextExtra) ← match field with
        | .extraData => pure (.extra extra, extra + 1)
        | .fixed value => pure (.fixed value, extra)
        | .quantity q => do
          let some (index, old) := findSource q.name source 0
            | throw s!"No source quantity named {q.name}"
          if q.unitsPerWhole == 0 || q.unitsPerWhole % old.unitsPerWhole != 0 then
            throw s!"No exact integer unit expansion for {q.name}"
          pure (.source index (q.unitsPerWhole / old.unitsPerWhole), extra)
      let (rules, totalExtras) ← visit rest nextExtra
      return (rule :: rules, totalExtras)

/-- A rejected inference cannot silently fall back to a dummy mapping. -/
def checkedMapping (result : Except String Mapping) :
    (match result with | .ok _ => True | .error _ => False) → Mapping :=
  match result with
  | .ok mapping => fun _ => mapping
  | .error _ => fun impossible => False.elim impossible

inductive Argument where
  | integer : Int → Argument
  | data : Data → Argument
  deriving Repr

def Argument.toTerm : Argument → Term
  | .integer n => .Const (.Integer n)
  | .data d => .Const (.Data d)

def Mapping.encode (mapping : Mapping) (source : List Int) (extras : List Data) :
    Option (List Argument) := do
  if source.length != mapping.sourceCount || extras.length != mapping.extraCount then none
  else mapping.rules.mapM fun
    | .source index factor => do return .integer ((← source[index]?) * (Int.ofNat factor))
    | .extra index => do return .data (← extras[index]?)
    | .fixed value => some (.integer value)

/-- The generated inverse recovers the original quantities and forgets new fields.
    Its round trip is proved for the inferred mapping in AutomaticMapping.lean.
    Arbitrary target values need not be in the image (e.g. fractional percentages). -/
def Mapping.recover (mapping : Mapping) (encoded : List Argument) : Option (List Int) :=
  if encoded.length != mapping.rules.length then none
  else (List.range mapping.sourceCount).mapM fun index => visit index mapping.rules encoded
where
  visit (index : Nat) : List Rule → List Argument → Option Int
    | .source i factor :: rules, .integer n :: values =>
        if i == index then some (n / Int.ofNat factor) else visit index rules values
    | _ :: rules, _ :: values => visit index rules values
    | _, _ => none

/-- Bad arity produces an evaluation error, never a successful default value. -/
def Mapping.arguments (mapping : Mapping) (source : List Int) (extras : List Data) : List Term :=
  match mapping.encode source extras with
  | some values => values.map Argument.toTerm
  | none => [Term.Error]

/-- Materialize a static mapping as a plain Lean argument builder before Blaster
    preprocessing. This avoids asking its optimizer to interpret the inference
    algorithm or a generic mapping interpreter on symbolic inputs. -/
syntax (name := mappingArgs) "#mapping_args " ident term : command

open Lean Elab Command in
@[command_elab mappingArgs]
unsafe def elaborateMappingArgs : CommandElab := fun stx => do
  let mapping ← liftTermElabM do
    let expr ← Lean.Elab.Term.elabTerm stx[2] (some (mkConst ``Mapping))
    Lean.Meta.evalExpr Mapping (mkConst ``Mapping) expr
  let mut binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  let mut inputs : Array (TSyntax `ident) := #[]
  let mut extras : Array (TSyntax `ident) := #[]
  for i in [:mapping.sourceCount] do
    let name := mkIdent (Name.mkSimple s!"input{i}")
    inputs := inputs.push name
    binders := binders.push (← `(bracketedBinder| ($name : Int)))
  for i in [:mapping.extraCount] do
    let name := mkIdent (Name.mkSimple s!"extra{i}")
    extras := extras.push name
    binders := binders.push (← `(bracketedBinder| ($name : PlutusCore.Data.Data)))
  let mut args : Array (TSyntax `term) := #[]
  for rule in mapping.rules do
    let value ← match rule with
      | .source i factor => do
        let some name := inputs[i]? | throwError "Invalid source index in mapping"
        if factor == 1 then
          `(PlutusCore.UPLC.Term.Term.Const (PlutusCore.UPLC.Term.Const.Integer $name))
        else
          `(PlutusCore.UPLC.Term.Term.Const
            (PlutusCore.UPLC.Term.Const.Integer ($name * $(quote factor))))
      | .extra i => do
        let some name := extras[i]? | throwError "Invalid extra index in mapping"
        `(PlutusCore.UPLC.Term.Term.Const (PlutusCore.UPLC.Term.Const.Data $name))
      | .fixed value => do
        let literal ← if value < 0 then `(-$(quote value.natAbs)) else pure (quote value.natAbs)
        `(PlutusCore.UPLC.Term.Term.Const (PlutusCore.UPLC.Term.Const.Integer $literal))
    args := args.push value
  let name : TSyntax `ident := ⟨stx[1]⟩
  elabCommand (← `(def $name $[$binders]* : List PlutusCore.UPLC.Term.Term := [$[$args],*]))

inductive OutputEncoding where
  | integer
  | dataInteger

def observe (encoding : OutputEncoding) : State → Option Int
  | .Halt (.VCon (.Integer n)) => match encoding with | .integer => some n | _ => none
  | .Halt (.VCon (.Data (.I n))) => match encoding with | .dataInteger => some n | _ => none
  | _ => none

-- Small AST helpers keep the two contract definitions in the example readable.
def int (n : Int) : Term := .Const (.Integer n)
def binary (op : BuiltinFun) (x y : Term) : Term := .Apply (.Apply (.Builtin op) x) y
def payout (amount rate : Term) (denominator : Int) : Term :=
  binary .DivideInteger (binary .MultiplyInteger amount rate) (int denominator)
def script (body : Term) : PlutusScript := ⟨.PlutusV3, .Program (.Version 1 1 0) body⟩

end Equivalence.MappingExamples.MappingSupport
