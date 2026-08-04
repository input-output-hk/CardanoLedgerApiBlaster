import CardanoLedgerApi.IsData.Class
import PlutusCore

namespace CardanoLedgerApi.V1.Value
open IsData.Class
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)

abbrev CurrencySymbol := ByteString
abbrev TokenName := ByteString

/-- The currency symbol for `Ada` -/
def adaSymbol : CurrencySymbol := ""

/-- The token name for `Ada` -/
def adaToken : TokenName := ""

/-- The 'Value' type is keep at the builtin level and is assumed to satisfy:
     - predicate validTxOutValue when is specified in a TxOut
     - predicate validMintValue when is specified in txInfoMint
-/
abbrev Value := List (Data × Data)

/-- BEq instance for Value -/
instance : BEq Value := ⟨List.beq⟩

/-- DecidableEq instance for Value -/
instance : DecidableEq Value := inferInstanceAs (DecidableEq Value)

/-! LawfulBEq instance for Value -/
instance : LawfulBEq Value := inferInstanceAs (LawfulBEq Value)

/-- IsData instance for ScriptHash -/
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

    The `Data` keys are destructured in the match patterns and the comparison is
    performed on the `ByteString` payloads, so no equality is ever *applied* at
    type `Data`.  This matters for the SMT toolchain: `Eq`/`BEq` on `Data` go
    through `eqData`, which lives in a `mutual` block, and a goal that still
    carries a `Data`-equality application over a symbolic `Value` cannot be
    translated.  Compare `PlutusCore.Value.lookupDataOuter`, which uses the same
    shape.

    **The rewrite is a pattern-split of the old condition, entry by entry.**
    `Data.B` is a constructor, hence injective and disjoint from
    `Data.Constr`/`Data.Map`/`Data.List`/`Data.I`.  Therefore
    `Data.B tn = r_tn` holds iff `r_tn` is of the form `Data.B b` with `b = tn`,
    which is exactly what the `(Data.B r_tn, r_price)` arm tests (with `==`,
    equivalent to `=` by `LawfulBEq ByteString`); the catch-all arm covers the
    keys for which the old condition was necessarily `false`, and takes the same
    `else` branch the old code took.  Behaviour on malformed entries is
    therefore identical to the old code:

    * `find_token`, key not a `B`: old condition `false`, recurse — new
      catch-all arm, recurse.
    * `find_token`, key matches but payload not an `I`: both return `0` and stop
      scanning.
    * `visit`, key not a `B` but payload a `Map`: old condition `false`, recurse
      — new `(_, Data.Map _)` arm, recurse.
    * `visit`, payload not a `Map`: both fall to the final catch-all and return
      `0` without scanning the tail.

    See `valueOf_eq_valueOfClassic` for the machine-checked statement of this
    argument against the previous definition, kept verbatim as `valueOfClassic`.
-/
def valueOf (cs : CurrencySymbol) (tn : TokenName) (v : Value) : Integer :=
  let rec find_token (tns : List (Data × Data)) : Integer :=
    match tns with
    | [] => 0
    | (Data.B r_tn, r_price) :: xs =>
        if tn == r_tn then
           match r_price with
           | Data.I price => price
           | _ => 0
        else find_token xs
    | _ :: xs => find_token xs
  let rec visit (v : Value) : Integer :=
    match v with
    | [] => 0
    | (Data.B r_cs, Data.Map tokens) :: xs =>
         if cs == r_cs
         then find_token tokens
         else visit xs
    | (_, Data.Map _) :: xs => visit xs
    | _ => 0
  visit v

/-- The previous definition of `valueOf`, kept verbatim so that the
    SMT-translatability rewrite can be checked against it in the kernel.
    See `valueOf_eq_valueOfClassic`.  Not exported; it exists only for the proof.
-/
private def valueOfClassic (cs : CurrencySymbol) (tn : TokenName) (v : Value) : Integer :=
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

private theorem valueOf_find_token_eq (tn : TokenName) (tns : List (Data × Data)) :
    valueOf.find_token tn tns = valueOfClassic.find_token tn tns := by
  induction tns with
  | nil => rfl
  | cons hd xs ih =>
      obtain ⟨r_tn, r_price⟩ := hd
      cases r_tn with
      | B b =>
          by_cases h : tn = b
          . subst h
            simp [valueOf.find_token, valueOfClassic.find_token]
          . simp [valueOf.find_token, valueOfClassic.find_token, h, ih]
      | Constr _ _ => simp [valueOf.find_token, valueOfClassic.find_token, ih]
      | Map _ => simp [valueOf.find_token, valueOfClassic.find_token, ih]
      | List _ => simp [valueOf.find_token, valueOfClassic.find_token, ih]
      | I _ => simp [valueOf.find_token, valueOfClassic.find_token, ih]

private theorem valueOf_visit_eq (cs : CurrencySymbol) (tn : TokenName) (v : Value) :
    valueOf.visit cs tn v = valueOfClassic.visit cs tn v := by
  induction v with
  | nil => rfl
  | cons hd xs ih =>
      obtain ⟨r_cs, r_price⟩ := hd
      cases r_price with
      | Map tokens =>
          cases r_cs with
          | B b =>
              by_cases h : cs = b
              . subst h
                simp [valueOf.visit, valueOfClassic.visit, valueOf_find_token_eq]
              . simp [valueOf.visit, valueOfClassic.visit, h, ih]
          | Constr _ _ => simp [valueOf.visit, valueOfClassic.visit, ih]
          | Map _ => simp [valueOf.visit, valueOfClassic.visit, ih]
          | List _ => simp [valueOf.visit, valueOfClassic.visit, ih]
          | I _ => simp [valueOf.visit, valueOfClassic.visit, ih]
      | Constr _ _ => cases r_cs <;> simp [valueOf.visit, valueOfClassic.visit]
      | List _ => cases r_cs <;> simp [valueOf.visit, valueOfClassic.visit]
      | I _ => cases r_cs <;> simp [valueOf.visit, valueOfClassic.visit]
      | B _ => cases r_cs <;> simp [valueOf.visit, valueOfClassic.visit]

/-- **Nothing changed.** The SMT-translatable `valueOf` agrees pointwise with the
    previous definition (`valueOfClassic`) on *every* `Value`, well-formed or not.
-/
theorem valueOf_eq_valueOfClassic (cs : CurrencySymbol) (tn : TokenName) (v : Value) :
    valueOf cs tn v = valueOfClassic cs tn v :=
  valueOf_visit_eq cs tn v


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
