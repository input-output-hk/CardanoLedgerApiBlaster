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

instance [IsData a] : IsData (Option a) where
  toData
  | none => mkDataConstr 1
  | some x => mkDataConstr 0 [IsData.toData x]
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
