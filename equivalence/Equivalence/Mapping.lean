import Equivalence.Function
import Lean

/-!
Schema-directed mappings for function comparisons. The source interface contains
integer quantities. The target can reorder and expand their units, accept arbitrary
extra Data arguments, and fix integer feature flags. Names and units are semantic
hints supplied by the caller, not inferred from UPLC or a blueprint.

Every source quantity must occur in the target with a positive integer scale.
The comparison covers all source integers and every value of each extra argument.
It makes no claim about target inputs outside this image (including other flags).
-/
namespace Equivalence.Mapping

open Lean
open PlutusCore.Data (Data)
open PlutusCore.UPLC.Term (Const)
open Acceptance (Result)

structure Quantity where
  name : String
  unitsPerWhole : Nat := 1
  deriving Repr, BEq, ToJson, FromJson

inductive TargetField where
  | quantity : Quantity → TargetField
  | extraData
  | fixed : Int → TargetField
  deriving Repr, BEq, ToJson, FromJson

inductive OutputEncoding where
  | constant
  | integer
  | dataInteger
  deriving Repr, BEq, ToJson, FromJson

structure Spec where
  source : List Quantity
  target : List TargetField
  oldOutput : OutputEncoding := .constant
  newOutput : OutputEncoding := .constant
  deriving Repr, BEq, ToJson, FromJson

inductive Rule where
  | source (index factor : Nat)
  | extra (index : Nat)
  | fixed (value : Int)
  deriving Repr, BEq, ToJson

structure Plan where
  sourceCount : Nat
  extraCount : Nat
  rules : List Rule
  deriving Repr, BEq, ToJson

private def uniqueNames : List Quantity → Bool
  | [] => true
  | q :: qs => !(qs.any fun other => q.name == other.name) && uniqueNames qs

/-- Reject lossy conversions, ambiguous names, and omission of any source field. -/
def infer (spec : Spec) : Except String Plan := do
  if !uniqueNames spec.source then throw "Ambiguous source quantity names"
  if spec.source.any (fun q => q.name.isEmpty) then throw "Source names must be nonempty"
  if spec.source.any (fun q => q.unitsPerWhole == 0) then throw "Source units must be positive"
  let mut rules := []
  let mut extras := 0
  for field in spec.target do
    match field with
    | .extraData =>
      rules := rules ++ [.extra extras]
      extras := extras + 1
    | .fixed value => rules := rules ++ [.fixed value]
    | .quantity q =>
      let some (old, index) := spec.source.zipIdx.find? (fun (old, _) => old.name == q.name)
        | throw s!"No source quantity named {q.name}"
      if q.unitsPerWhole == 0 || q.unitsPerWhole % old.unitsPerWhole != 0 then
        throw s!"No exact integer unit expansion for {q.name}"
      rules := rules ++ [.source index (q.unitsPerWhole / old.unitsPerWhole)]
  unless (List.range spec.source.length).all (fun index => rules.any fun
      | .source i _ => i == index
      | _ => false) do
    throw "A source quantity is missing from the target"
  return ⟨spec.source.length, extras, rules⟩

def integer (n : Int) : PlutusCore.UPLC.Term.Term := .Const (.Integer n)

/-- Native interpreter, used to replay the original programs on mapped arguments. -/
def Plan.encode (plan : Plan) (source : List Int) (extras : List Data) :
    Option (List PlutusCore.UPLC.Term.Term) := do
  if source.length != plan.sourceCount || extras.length != plan.extraCount then none
  else plan.rules.mapM fun
    | .source index factor => do return integer ((← source[index]?) * Int.ofNat factor)
    | .extra index => do return .Const (.Data (← extras[index]?))
    | .fixed value => some (integer value)

/-- Left inverse on encoded inputs. This is not a validator for arbitrary target
    arguments: fixed fields and extras are deliberately projected away. -/
def Plan.recover (plan : Plan) (args : List PlutusCore.UPLC.Term.Term) : Option (List Int) := do
  if args.length != plan.rules.length then none
  else (List.range plan.sourceCount).mapM fun index => do
    let some (.source _ factor, .Const (.Integer n)) :=
      (plan.rules.zip args).find? (fun (rule, _) => match rule with
        | .source i _ => i == index
        | _ => false) | none
    if factor == 0 || n % Int.ofNat factor != 0 then none
    else some (n / Int.ofNat factor)

def decode : OutputEncoding → Const → Option Const
  | .constant, value => some (Function.normalize value)
  | .integer, .Integer n => some (.Integer n)
  | .dataInteger, .Data (.I n) => some (.Integer n)
  | _, _ => none

/-- A failed output decoding is unknown, never agreement between two missing
    values. Evaluation errors and exhaustion retain strict function semantics. -/
def same (oldEncoding newEncoding : OutputEncoding) : Result → Result → Option Bool
  | .success (.VCon old) _, .success (.VCon new) _ => do
    return (← decode oldEncoding old) == (← decode newEncoding new)
  | .error, .error => some true
  | .success _ _, .error | .error, .success _ _ => some false
  | _, _ => none

instance : ToExpr OutputEncoding where
  toTypeExpr := mkConst ``OutputEncoding
  toExpr
    | .constant => mkConst ``OutputEncoding.constant
    | .integer => mkConst ``OutputEncoding.integer
    | .dataInteger => mkConst ``OutputEncoding.dataInteger

open Meta
private partial def withInputs (types : List (Name × Expr))
    (k : Array Expr → MetaM Expr) (vars : Array Expr := #[]) : MetaM Expr :=
  match types with
  | [] => do mkForallFVars vars (← k vars)
  | (name, type) :: rest => withLocalDeclD name type fun var =>
      withInputs rest k (vars.push var)

/-- Generate concrete list spines and direct arithmetic before Blaster sees the
    query. The inference algorithm is never interpreted on symbolic inputs. -/
def proposition (spec : Spec) (old new : Expr) (cpu memory : Nat)
    (v3 budgeted : Bool) (steps : Nat) : MetaM Expr := do
  let plan ← ofExcept (infer spec)
  let types := (List.range plan.sourceCount).map (fun i =>
      (Name.mkSimple s!"input{i}", mkConst ``Int)) ++
    (List.range plan.extraCount).map (fun i =>
      (Name.mkSimple s!"extra{i}", mkConst ``Data))
  let goal ← withInputs types fun vars => do
    let toInteger := fun n => mkApp (mkConst ``integer) n
    let oldArgs ← mkListLit (mkConst ``PlutusCore.UPLC.Term.Term)
      ((vars.extract 0 plan.sourceCount).toList.map toInteger)
    let newArgs ← plan.rules.mapM fun
      | .source index factor => do
        let some input := vars[index]? | throwError "Invalid source index in mapping"
        let value := if factor == 1 then input else
          mkApp2 (mkConst ``Int.mul) input (toExpr (Int.ofNat factor))
        return toInteger value
      | .extra index => do
        let some input := vars[plan.sourceCount + index]? | throwError "Invalid extra index in mapping"
        return mkApp (mkConst ``PlutusCore.UPLC.Term.Term.Const) (mkApp (mkConst ``Const.Data) input)
      | .fixed value => pure (toInteger (toExpr value))
    let newArgs ← mkListLit (mkConst ``PlutusCore.UPLC.Term.Term) newArgs
    let execute := fun program args => mkAppN (mkConst ``Function.execute)
      #[program, args, toExpr cpu, toExpr memory, toExpr v3, toExpr budgeted, toExpr steps]
    let comparison := mkAppN (mkConst ``same)
      #[toExpr spec.oldOutput, toExpr spec.newOutput, execute old oldArgs, execute new newArgs]
    mkEq comparison (toExpr (some true))
  check goal
  return goal

end Equivalence.Mapping
