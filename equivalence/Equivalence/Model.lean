import PlutusCore.Data

namespace Equivalence.Model

open PlutusCore.Data (Data)
open Lean (Json toJson)

private inductive SExpr where
  | atom : String → SExpr
  | text : String → SExpr
  | list : List SExpr → SExpr

private def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- SMT-LIB uses doubled quotes and Unicode escapes in strings. -/
private partial def text (acc : List Char) : List Char → Option (String × List Char)
  | '"' :: '"' :: rest => text ('"' :: acc) rest
  | '"' :: rest => some (String.mk acc.reverse, rest)
  | '\\' :: 'u' :: '{' :: rest => do
    let (digits, rest) := rest.span (· != '}')
    let '}' :: rest := rest | none
    let code ← digits.foldlM (fun n c => return n * 16 + (← hexDigit c)) 0
    text (Char.ofNat code :: acc) rest
  | c :: rest => text (c :: acc) rest
  | [] => none

private partial def parse : List Char → Option (SExpr × List Char)
  | input => do
    let input := input.dropWhile Char.isWhitespace
    match input with
    | '(' :: rest => do
      let (items, rest) ← items [] rest
      return (.list items, rest)
    | '"' :: rest => do
      let (s, rest) ← text [] rest
      return (.text s, rest)
    | [] => none
    | ')' :: _ => none
    | _ =>
      let (word, rest) := input.span (fun c => !c.isWhitespace && c != '(' && c != ')')
      return (.atom (String.mk word), rest)
where
  items (acc : List SExpr) (input : List Char) : Option (List SExpr × List Char) := do
    let input := input.dropWhile Char.isWhitespace
    match input with
    | ')' :: rest => return (acc.reverse, rest)
    | [] => none
    | _ =>
      let (item, rest) ← parse input
      items (item :: acc) rest

private def integer : SExpr → Option Int
  | .atom n => n.toInt?
  | .list [.atom "-", .atom n] => return -(Int.ofNat (← n.toNat?))
  | _ => none

/-- Constructor names carry a monomorphization suffix for polymorphic datatypes. -/
private def constructor (name suffix : String) : Bool :=
  name == suffix || name.endsWith ("." ++ suffix) || name.startsWith (suffix ++ "_")

private partial def dataValue : SExpr → Option Data
  | .list [.atom ctor, n] =>
    if constructor ctor "I" then return .I (← integer n)
    else if constructor ctor "B" then
      match n with
      | .list [.atom maker, .text bytes] =>
        if constructor maker "mk" && bytes.data.all (fun c => c.toNat < 256)
        then some (.B ⟨bytes⟩) else none
      | _ => none
    else if constructor ctor "List" then return .List (← dataList n)
    else if constructor ctor "Map" then return .Map (← pairList n)
    else none
  | .list [.atom ctor, tag, fields] =>
    if constructor ctor "Constr" then return .Constr (← integer tag) (← dataList fields)
    else none
  | _ => none
where
  dataList : SExpr → Option (List Data)
    | .atom ctor => if ctor.startsWith "List.nil" then some [] else none
    | .list [.atom "as", value, _] => dataList value
    | .list [.atom ctor, head, tail] =>
      if ctor.startsWith "List.cons" then return (← dataValue head) :: (← dataList tail) else none
    | _ => none
  pairList : SExpr → Option (List (Data × Data))
    | .atom ctor => if ctor.startsWith "List.nil" then some [] else none
    | .list [.atom "as", value, _] => pairList value
    | .list [.atom ctor, .list [.atom pair, key, value], tail] =>
      if ctor.startsWith "List.cons" && pair.startsWith "Prod.mk" then
        return ((← dataValue key), (← dataValue value)) :: (← pairList tail)
      else none
    | _ => none

private def bindingValue (binding : String) : Option (String × SExpr) := do
  let name :: parts := binding.splitOn ": " | none
  unless !parts.isEmpty do none
  let (value, rest) ← parse (": ".intercalate parts).data
  unless (rest.dropWhile Char.isWhitespace).isEmpty do none
  return (name.trim, value)

def dataBinding (binding : String) : Option (String × Data) := do
  let (name, value) ← bindingValue binding
  return (name, ← dataValue value)

def integerBinding (binding : String) : Option (String × Int) := do
  let (name, value) ← bindingValue binding
  return (name, ← integer value)

/-- Vesting's shape constraints expose list/map/bytestring binders directly,
    rather than wrapped in a Data constructor. Reuse the same strict decoder. -/
private def wrappedBinding (wrapper : String) (binding : String) : Option (String × Data) := do
  let (name, value) ← bindingValue binding
  return (name, ← dataValue (.list [.atom wrapper, value]))

def listBinding (binding : String) : Option (String × List Data) := do
  let (name, .List items) ← wrappedBinding "Data.List" binding | none
  return (name, items)

def mapBinding (binding : String) : Option (String × List (Data × Data)) := do
  let (name, .Map items) ← wrappedBinding "Data.Map" binding | none
  return (name, items)

def byteStringBinding (binding : String) : Option (String × PlutusCore.ByteString.ByteString) := do
  let (name, .B bytes) ← wrappedBinding "Data.B" binding | none
  return (name, bytes)

partial def dataJson : Data → Json
  | .I n => Json.mkObj [("int", toJson n)]
  | .B bytes => Json.mkObj [("bytes", toJson <| String.join <|
      bytes.data.data.map (fun c => UInt8.toBitVec c.toUInt8 |>.toHex))]
  | .Constr tag fields => Json.mkObj [("constructor", toJson tag), ("fields", toJson (fields.map dataJson))]
  | .List items => Json.mkObj [("list", toJson (items.map dataJson))]
  | .Map pairs => Json.mkObj [("map", toJson (pairs.map fun (k, v) =>
      Json.mkObj [("k", dataJson k), ("v", dataJson v)]))]

end Equivalence.Model
