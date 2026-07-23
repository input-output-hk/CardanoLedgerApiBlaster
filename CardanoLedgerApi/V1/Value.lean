import CardanoLedgerApi.IsData.Class
import PlutusCore

namespace CardanoLedgerApi.V1.Value
open IsData.Class
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)

def CurrencySymbol : Type := ByteString

instance : Repr CurrencySymbol := inferInstanceAs (Repr ByteString)

/-- BEq instance for CurrencySymbol -/
instance : BEq CurrencySymbol := inferInstanceAs (BEq ByteString)

/-! LawfulBEq instance for CurrencySymbol -/
instance : LawfulBEq CurrencySymbol := inferInstanceAs (LawfulBEq ByteString)

/-! DecidableEq instance for CurrencySymbol -/
instance : DecidableEq CurrencySymbol := inferInstanceAs (DecidableEq ByteString)

/-- LT instance for CurrencySymbol -/
instance : LT CurrencySymbol := inferInstanceAs (LT ByteString)

/-- DecidableLT instance for TxOutRef -/
instance : DecidableLT (CurrencySymbol) := inferInstanceAs (DecidableLT ByteString)

@[simp] theorem beqCurrencySymbol_iff_eq (x y : CurrencySymbol) : x == y ↔ x = y := by simp [BEq.beq]

@[simp] theorem beqCurrencySymbol_false_iff_not_eq (x y : CurrencySymbol) : (x == y) = false ↔ x ≠ y := by simp [BEq.beq]

/-- Std.Irrefl instance for CurrencySymbol -/
instance : Std.Irrefl (. < . : CurrencySymbol → CurrencySymbol → Prop) :=
  inferInstanceAs (Std.Irrefl (. < . : ByteString → ByteString → Prop))

/-- LE instance for CurrencySymbol -/
instance : LE CurrencySymbol := inferInstanceAs (LE ByteString)

/-- DecidableLE instance for CurrencySymbol -/
instance : DecidableLE CurrencySymbol := inferInstanceAs (DecidableLE ByteString)

/-- ToString instance for CurrencySymbol -/
instance : ToString CurrencySymbol := inferInstanceAs (ToString ByteString)

/-- String to CurrencySymbol coercion to mimick OverloadedString in Haskell -/
instance : Coe String CurrencySymbol := inferInstanceAs (Coe String ByteString)

/-- IsData instance for CurrencySymbol -/
instance : IsData CurrencySymbol := inferInstanceAs (IsData ByteString)


def TokenName : Type := ByteString

instance : Repr TokenName := inferInstanceAs (Repr ByteString)

/-- BEq instance for TokenName -/
instance : BEq TokenName := inferInstanceAs (BEq ByteString)

/-! LawfulBEq instance for TokenName -/
instance : LawfulBEq TokenName := inferInstanceAs (LawfulBEq ByteString)

/-! DecidableEq instance for TokenName -/
instance : DecidableEq TokenName := inferInstanceAs (DecidableEq ByteString)

/-- LT instance for TokenName -/
instance : LT TokenName := inferInstanceAs (LT ByteString)

/-- DecidableLT instance for TxOutRef -/
instance : DecidableLT (TokenName) := inferInstanceAs (DecidableLT ByteString)

@[simp] theorem beqTokenName_iff_eq (x y : TokenName) : x == y ↔ x = y := by simp [BEq.beq]

@[simp] theorem beqTokenName_false_iff_not_eq (x y : TokenName) : (x == y) = false ↔ x ≠ y := by simp [BEq.beq]

/-- Std.Irrefl instance for TokenName -/
instance : Std.Irrefl (. < . : TokenName → TokenName → Prop) :=
  inferInstanceAs (Std.Irrefl (. < . : ByteString → ByteString → Prop))

/-- LE instance for TokenName -/
instance : LE TokenName := inferInstanceAs (LE ByteString)

/-- DecidableLE instance for TokenName -/
instance : DecidableLE TokenName := inferInstanceAs (DecidableLE ByteString)

/-- ToString instance for TokenName -/
instance : ToString TokenName := inferInstanceAs (ToString ByteString)

/-- String to TokenName coercion to mimick OverloadedString in Haskell -/
instance : Coe String TokenName := inferInstanceAs (Coe String ByteString)

/-- IsData instance for TokenName -/
instance : IsData TokenName := inferInstanceAs (IsData ByteString)


/-- The currency symbol for `Ada` -/
def adaSymbol : CurrencySymbol := ""

/-- The token name for `Ada` -/
def adaToken : TokenName := ""

/-- The 'Value' type is keep at the builtin level and is assumed to satisfy:
     - predicate validTxOutValue when is specified in a TxOut
     - predicate validMintValue when is specified in txInfoMint
-/
def Value : Type := List (Data × Data)

instance : Repr Value := inferInstanceAs (Repr (List (Data × Data)))

/-- BEq instance for Value -/
instance : BEq Value := ⟨List.beq⟩

/-- DecidableEq instance for Value -/
instance : DecidableEq Value := inferInstanceAs (DecidableEq (List (Data × Data)))

/-! LawfulBEq instance for Value -/
instance : LawfulBEq Value := inferInstanceAs (LawfulBEq (List (Data × Data)))


/-- IsData instance for Value -/
instance : IsData Value where
  toData v := Data.Map v
  fromData
  | Data.Map v => some v
  | _ => none


/-! Helpers -/

/-- Construct a null `Value` with nothing in it -/
def null : Value := []

/-- Return a `Value` containing only the given quantity for the
    given currency symbol `cs` and token name `n`
-/
def singleton (cs : CurrencySymbol) (tn : TokenName) (n : Integer) : Value :=
  [(Data.B cs, Data.Map [(Data.B tn, Data.I n)])]

/-- return a `Value` containing only the given quantity of Lovelace -/
def lovelaceValue (n : Integer) : Value :=
  singleton adaSymbol adaToken n


/-- Return the quantity of Lovelace in Value `v`.
    Assume that value satisfies either `validTxOutValue` or `validMintValue`.
-/
def lovelaceOf (v : Value) : Integer :=
  match v with
  | (Data.B "", Data.Map [(Data.B "", Data.I n)]) :: _ => n
  | _ => 0

/-- Return a Value containing only Ada, if any.
    Assume that value satisfies either `validTxOutValue` or `validMintValue`.
-/
def onlyLovelace (v : Value) : Value :=
  match v with
  | p@(Data.B "", Data.Map [(Data.B "", Data.I _)]) :: _ => [p]
  | _ => null

/-- Return a Value excluding Ada.
    Assume that value satisfies either `validTxOutValue` or `validMintValue`.
-/
def withoutLovelace (v : Value) : Value :=
  match v with
  | (Data.B "", Data.Map [(Data.B "", Data.I _)]) :: rest => rest
  | _ => v

/-- Return the quantity for the given currency symbol `cs` and the
    given token name `tn` in Value `v`.
-/
def valueOf (cs : CurrencySymbol) (tn : TokenName) (v : Value) : Integer :=
  let rec find_token (tns : List (Data × Data)) : Integer :=
    match tns with
    | [] => 0
    | (r_tn, r_price) :: xs =>
        if Data.B tn = r_tn then
           match r_price with
           | Data.I price => price
           | _ => 0
        else find_token xs
  let rec visit (v : Value) : Integer :=
    match v with
    | [] => 0
    | (r_cs, Data.Map tokens) :: xs =>
         if Data.B cs == r_cs
         then find_token tokens
         else visit xs
    | _ => 0
  visit v


/-- Add a (positive or negative) quantity of a single token to Value `v`.
    If the token is already present in `v` the quantity is incremented/decremented accordingly.
    The token is removed from `v` if the resulting quantity is zero.
    Assume that value satisfies either `validTxOutValue` or `validMintValue`.
-/
def add (cs : CurrencySymbol) (tn : TokenName) (n : Integer) (v : Value) : Value :=
  let rec tn_visit (tns : List (Data × Data)) : List (Data × Data) :=
    match tns with
    | [] => [(Data.B tn, Data.I n)]
    | p@(Data.B tn', Data.I n') :: xs =>
         if tn < tn' then (Data.B tn, Data.I n) :: tns
         else if tn == tn' then
           let qty := n' + n
           if qty == 0 then xs
           else (Data.B tn, Data.I qty) :: xs
         else p :: (tn_visit xs)
    | _ => tns -- unreachable, i.e., token map is well-formed
  let rec cs_visit (v : Value) : Value :=
   match v with
   | [] => singleton cs tn n
   | p@(Data.B cs', Data.Map tokens) :: xs =>
       if cs < cs' then (Data.B cs, Data.Map [(Data.B tn, Data.I n)]) :: v
       else if cs == cs' then (Data.B cs', Data.Map (tn_visit tokens)) :: xs
       else p :: cs_visit xs
   | _ => v -- unreachable case, i.e., Value is well-formed
  if n == 0 then v
  else cs_visit v

/-- Combine two `Value` together
    Assume that the `Value` instances satisfy either `validTxOutValue` or `validMintValue`.
-/
def merge (v1 : Value) (v2 : Value) : Value :=
 let rec tn_visit (left : List (Data × Data)) (right : List (Data × Data)) : List (Data × Data) :=
   match left, right with
   | [], _ => right
   | _, [] => left
   | left'@(p1@(Data.B tn, Data.I n) :: xs), right'@(p2@(Data.B tn', Data.I n') :: xs') =>
        if tn < tn' then p1 :: tn_visit xs right'
        else if tn == tn' then
          let qty := n + n'
          if qty == 0 then tn_visit xs xs'
          else (Data.B tn, Data.I qty) :: tn_visit xs xs'
        else p2 :: tn_visit left' xs'
   | _, _ => right -- assume token map is well-formed
   termination_by left.length + right.length
 let rec cs_visit (left : Value) (right : Value) : Value :=
   match left, right with
   | [], _ => right
   | _, [] => left
   | left'@(p1@(Data.B cs, Data.Map tokens) :: xs), right'@(p2@(Data.B cs', Data.Map tokens') :: xs') =>
        if cs < cs' then p1 :: cs_visit xs right'
        else if cs == cs' then
           match tn_visit tokens tokens' with
           | [] => cs_visit xs xs'
           | new_tokens => (Data.B cs, Data.Map new_tokens) :: cs_visit xs xs'
        else p2 :: cs_visit left' xs'
   | _, _ => right -- assume Value is well-formed
   termination_by left.length + right.length
 cs_visit v1 v2


/-! Predicates -/

/-- Check if the currency symbol `cs` is present in Value `v`. -/
def hasCurrencySymbol (cs : CurrencySymbol) (v : Value) : Bool :=
 match v with
 | [] => false
 | x :: xs => Data.B cs == x.1 || hasCurrencySymbol cs xs

/-- Check if the currency symbol `cs` is present in Value `v`.
    Other assets (other than Ada) are not tolerated.
    Assume that value satisfies either `validTxOutValue` or `validMintValue`.
-/
def hasOnlyCurrencySymbol (cs : CurrencySymbol) (v : Value) : Bool :=
 match v with
 | _ada :: [(Data.B cs', _)] => cs' == cs
 | _ => false

/-- Check if Value only contains non-zero Ada. -/
def hasOnlyNonZeroAda (v : Value) : Bool :=
  match v with
  | [ (Data.B "", Data.Map [(Data.B "", Data.I n)]) ] => n > 0
  | _ => false

end CardanoLedgerApi.V1.Value
