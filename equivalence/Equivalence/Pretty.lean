import Lean

/-! Human-readable views of checker reports. JSON remains the machine interface.
Named context fields follow the V3 ScriptContext/TxInfo encoding; opaque payloads
retain their exact textual Plutus Data representation. -/

namespace Equivalence.Pretty
open Lean

private def field (value : Json) (name : String) : Option Json :=
  (value.getObjVal? name).toOption

private def array (value : Json) (name : String) : Option (Array Json) :=
  (value.getObjValAs? (Array Json) name).toOption

private def integer (value : Json) : Option Int :=
  (value.getObjValAs? Int "int").toOption

private def bytes (value : Json) : Option String :=
  (value.getObjValAs? String "bytes").toOption

private def constructor (value : Json) : Option (Int × Array Json) := do
  return (← (value.getObjValAs? Int "constructor").toOption, ← array value "fields")

/-- Exact raw payload syntax, also accepted by the CLI's explicit Data parser. -/
partial def dataText (value : Json) : Option String := do
  if let some n := integer value then return s!"I {n}"
  if let some hex := bytes value then return s!"B #{hex}"
  if let some (tag, fields) := constructor value then
    return s!"Constr {tag} [{String.intercalate ", " (← fields.toList.mapM dataText)}]"
  if let some items := array value "list" then
    return s!"List [{String.intercalate ", " (← items.toList.mapM dataText)}]"
  if let some entries := array value "map" then
    let pairs ← entries.toList.mapM fun entry => do
      return s!"({← dataText (← field entry "k")}, {← dataText (← field entry "v")})"
    return s!"Map [{String.intercalate ", " pairs}]"
  none

private def raw (value : Json) : String := (dataText value).getD value.compress

private def groupedNat (n : Nat) : String := Id.run do
  let mut parts := []
  let mut rest := n
  while rest ≥ 1000 do
    let digits := toString (rest % 1000)
    parts := (String.mk (List.replicate (3 - digits.length) '0') ++ digits) :: parts
    rest := rest / 1000
  return String.intercalate "," (toString rest :: parts)

private def grouped (n : Int) : String :=
  (if n < 0 then "-" else "") ++ groupedNat n.natAbs

private def lovelace (n : Int) : String :=
  let fraction := toString (n.natAbs % 1000000)
  let ada := (if n < 0 then "-" else "") ++ toString (n.natAbs / 1000000) ++ "." ++
    String.mk (List.replicate (6 - fraction.length) '0') ++ fraction
  s!"{grouped n} lovelace ({ada} ADA)"

private def reference (value : Json) : Option String := do
  let (0, fields) ← constructor value | none
  unless fields.size == 2 do none
  let hash ← bytes fields[0]!
  let index ← integer fields[1]!
  return s!"{if hash.isEmpty then "(empty tx id)" else hash}#{index}"

private def credential (value : Json) : Option String := do
  let (tag, fields) ← constructor value
  unless fields.size == 1 do none
  let hash ← bytes fields[0]!
  let kind ← if tag == 0 then some "pubkey" else if tag == 1 then some "script" else none
  return s!"{kind} #{hash}"

private def address (value : Json) : String := ((do
  let (0, fields) ← constructor value | none
  unless fields.size == 2 do none
  let payment ← credential fields[0]!
  let (tag, stake) ← constructor fields[1]!
  if tag == 1 && stake.isEmpty then return payment ++ "; stake: none"
  if tag == 0 && stake.size == 1 then return payment ++ "; stake: " ++ raw stake[0]!
  none) : Option String).getD (raw value)

private def valueText (value : Json) : String := ((do
  let policies ← array value "map"
  let groups ← policies.toList.mapM fun policy => do
    let id ← bytes (← field policy "k")
    let tokens ← array (← field policy "v") "map"
    tokens.toList.mapM fun token => do
      let name ← bytes (← field token "k")
      let quantity ← integer (← field token "v")
      return if id.isEmpty && name.isEmpty then lovelace quantity
        else s!"{grouped quantity} token #{id}.#{name}"
  let entries := groups.flatten
  return if entries.isEmpty then "empty" else String.intercalate "; " entries) : Option String).getD (raw value)

private def datumText (value : Json) : String :=
  match constructor value with
  | some (0, #[]) => "none"
  | some (1, #[hash]) => "hash " ++ raw hash
  | some (2, #[datum]) => "inline " ++ raw datum
  | _ => raw value

private def optionalData (value : Json) : String :=
  match constructor value with
  | some (1, #[]) => "none"
  | some (0, #[payload]) => raw payload
  | _ => raw value

private def bound (value : Json) : Option (String × Bool) := do
  let (0, fields) ← constructor value | none
  unless fields.size == 2 do none
  let (extended, payload) ← constructor fields[0]!
  let text ← match extended, payload with
    | 0, #[] => some "-∞"
    | 1, #[n] => (integer n).map grouped
    | 2, #[] => some "+∞"
    | _, _ => none
  let (closure, #[]) ← constructor fields[1]! | none
  unless closure == 0 || closure == 1 do none
  return (text, closure == 1)

private def interval (value : Json) : String := ((do
  let (0, fields) ← constructor value | none
  unless fields.size == 2 do none
  let (lower, closedLower) ← bound fields[0]!
  let (upper, closedUpper) ← bound fields[1]!
  return (if closedLower then "[" else "(") ++ lower ++ ", " ++ upper ++
    (if closedUpper then "]" else ")")) : Option String).getD (raw value)

private def outputLines (value : Json) (indent : String) : List String :=
  match constructor value with
  | some (0, #[addr, amount, datum, script]) => [
      indent ++ "Address: " ++ address addr,
      indent ++ "Value: " ++ valueText amount,
      indent ++ "Datum: " ++ datumText datum,
      indent ++ "Reference script: " ++ optionalData script]
  | _ => [indent ++ raw value]

private def inputLines (value : Json) (indent : String) (own : Option String) : List String :=
  match constructor value with
  | some (0, #[ref, output]) =>
    let label := (reference ref).getD (raw ref)
    (indent ++ "Reference: " ++ label ++ (if own == some label then " (spending input)" else "")) ::
      outputLines output indent
  | _ => [indent ++ raw value]

private def collection (label : String) (value : Json) (render : Json → List String) : List String :=
  match array value "list" with
  | some #[] => ["  " ++ label ++ ": none"]
  | some items => ("  " ++ label ++ ":") :: items.toList.zipIdx.flatMap fun (item, i) =>
      (s!"    [{i}]") :: render item
  | none => ["  " ++ label ++ ": " ++ raw value]

/-- Render every TxInfo field with ledger names, keeping hashes and payloads intact. -/
def context (value : Json) : Option (List String) := do
  let (0, #[tx, redeemer, info]) ← constructor value | none
  let (0, fields) ← constructor tx | none
  unless fields.size == 16 do none
  let (own, purpose) ← match constructor info with
    | some (1, #[ref, datum]) =>
      let own := reference ref
      some (own, ["  Spending input: " ++ own.getD (raw ref), "  Datum: " ++ optionalData datum])
    | some (0, #[symbol]) => some (none, ["  Minting policy: " ++ raw symbol])
    | _ => none
  let hash := (bytes fields[11]!).map ("#" ++ ·) |>.getD (raw fields[11]!)
  let fee := (integer fields[3]!).map lovelace |>.getD (raw fields[3]!)
  let mut lines := ["  Context:", "  Transaction id: " ++ hash] ++ purpose ++ [
    "  Redeemer: " ++ raw redeemer,
    "  Fee: " ++ fee, "  Validity range (POSIX ms): " ++ interval fields[7]!]
  lines := lines ++ collection "Inputs" fields[0]! (fun input => inputLines input "      " own)
  lines := lines ++ collection "Reference inputs" fields[1]! (fun input => inputLines input "      " none)
  lines := lines ++ collection "Outputs" fields[2]! (fun output => outputLines output "      ")
  let signers := (array fields[8]! "list").map fun items =>
    if items.isEmpty then "none" else String.intercalate ", " (items.toList.map raw)
  lines := lines ++ ["  Signers: " ++ signers.getD (raw fields[8]!), "  Mint: " ++ valueText fields[4]!]
  for (label, index) in [("Certificates", 5), ("Withdrawals", 6), ("Redeemers", 9),
      ("Datums", 10), ("Votes", 12), ("Proposals", 13), ("Treasury", 14), ("Donation", 15)] do
    lines := lines ++ ["  " ++ label ++ ": " ++ raw fields[index]!]
  return lines.head! :: lines.tail.map ("  " ++ ·)

private def resultText (value : Json) : String := Id.run do
  let accepts := (value.getObjValAs? Bool "accepts").toOption
  let kind := (value.getObjValAs? String "kind").toOption
  let result := field value "result"
  let detail := match kind with
    | some "error" => "error"
    | some "budget_exhausted" => "budget exhausted"
    | some "unfinished" => "step limit reached"
    | some other => other
    | none => ""
  let payload := result.map (fun r =>
    let kind := (r.getObjValAs? String "kind").toOption.getD "value"
    (field r "value").map (fun n => kind ++ " " ++ n.compress) |>.getD kind)
  let description := payload.getD detail
  let status := match accepts with
    | some true => "accepts"
    | some false => "rejects"
    | none => "outcome"
  let mut text := status ++ (if description.isEmpty then "" else " (" ++ description ++ ")")
  for (key, label) in [("spent_cpu", "CPU"), ("spent_memory", "memory")] do
    if let .ok n := value.getObjValAs? Nat key then text := text ++ s!"; {label}: {groupedNat n}"
  return text

/-- Function inputs stay Data/integers; only validator inputs are interpreted as contexts. -/
def counterexample (validator : Bool) (witness : Json) : String := Id.run do
  let mut lines := ["Counterexample:"]
  if let .ok direction := witness.getObjValAs? String "direction" then
    lines := lines ++ ["  Direction: " ++ (if direction == "old_to_new" then "OLD → NEW"
      else if direction == "new_to_old" then "NEW → OLD" else direction)]
  for name in ["old", "new"] do
    if let some result := field witness name then
      lines := lines ++ ["  " ++ name.toUpper ++ ": " ++ resultText result]
  if let .ok replayed := witness.getObjValAs? Bool "replayed" then
    lines := lines ++ ["  Replay: " ++ if replayed then "confirmed" else "unconfirmed"]
  if let some validity := field witness "ledger_validity" then
    if let .ok valid := validity.getObjValAs? Bool "valid" then
      lines := lines ++ ["  Ledger validation: " ++ if valid then "valid (ledger model)" else "invalid"]
  if let some input := field witness "input" then
    if validator then
      if let some rendered := context input then
        return String.intercalate "\n" (lines ++ rendered)
    if let some datum := field input "datum" then
      lines := lines ++ ["  Datum: " ++ raw datum]
      if let some redeemer := field input "redeemer" then lines := lines ++ ["  Redeemer: " ++ raw redeemer]
      if let some ctx := field input "context" then lines := lines ++ ["  Context (Data): " ++ raw ctx]
    else lines := lines ++ ["  Input: " ++ raw input]
  else lines := lines ++ ["  Details: " ++ witness.pretty]
  return String.intercalate "\n" lines

end Equivalence.Pretty
