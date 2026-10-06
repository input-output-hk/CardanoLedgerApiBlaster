import PlutusCore

namespace CardanoLedgerApi.IsData.Class
open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term (Const Term)


-- | A typeclass for types that can be converted to and from 'Data'.
class IsData (α : Type u) where
  toData : α → Data
  fromData : Data → Option α

def mkDataConstr (tag : Integer) (fields : List Data := []) : Data :=
  Data.Constr tag fields

/-- `Data`-encode a ledger value with the ledger's own encoding.

The same thing as `IsData.toData`, under a name that cannot collide. There are
two structurally identical `IsData` classes in play — this one and
`PlutusCore.IsData` — and a property stated against a compiled validator has
both in scope: the ledger types come from here, the generated blueprint types
from there. `IsData.toData` is ambiguous in that scope; this is not.

Reducible, so it disappears before a solver sees the term. -/
abbrev toLedgerData {a : Type u} [IsData a] (x : a) : Data := IsData.toData x

instance : IsData Data where
  toData x := x
  fromData x := x

instance : IsData Integer where
  toData := Data.I
  fromData
  | Data.I x => some x
  | _ => none

instance : IsData ByteString where
  toData := Data.B
  fromData
  | Data.B bs => some bs
  | _ => none

instance : IsData Bool where
  toData b := if b then mkDataConstr 1 else mkDataConstr 0
  fromData
  | Data.Constr n [] =>
      if n = 0 then some false
      else if n = 1 then some true
      else none
  | _ => none

/-- `toData` for `Option`, as a named function so it can be tagged below.
    Blaster keeps tagged functions folded (a single application node) when the
    argument is symbolic; inlined, this `match` would otherwise sit stuck
    inside converted `Data` trees and be re-optimized on every revisit of the
    machine state during `#prep_uplc`. -/
def optionToData [IsData a] : Option a → Data
  | none => mkDataConstr 1
  | some x => mkDataConstr 0 [IsData.toData x]

open Lean Elab Command in
run_cmd liftTermElabM do
  discard <| Lean.Meta.getUnfoldEqnFor? ``optionToData (nonRec := true)
  Lean.Meta.markAsRecursive ``optionToData

instance [IsData a] : IsData (Option a) where
  toData := optionToData
  fromData
  | Data.Constr 1 [] => some none
  | Data.Constr 0 [r_data] =>
      match IsData.fromData r_data with
      | none => none
      | some x => some (some x)
  | _ => none

/-- Convert any type having `IsData` instance to a UPLC term. -/
def toTerm [IsData α] (x : α) : Term := Term.Const (Const.Data (IsData.toData x))

end CardanoLedgerApi.IsData.Class
