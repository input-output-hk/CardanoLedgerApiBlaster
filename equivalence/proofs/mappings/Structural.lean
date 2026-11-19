import CardanoLedgerApi.IsData.Class

/-!
Structural input mappings for the equivalence CLI design. Run from the repository root:
  lake env lean equivalence/proofs/mappings/Structural.lean

This tests mapping and codec laws, not the equivalence of existing compiled contracts.
The Lean types/codecs stand in for generated blueprint bindings. The mapping is
written explicitly; this example does not implement an automatic inference engine.

Simulated user correspondences:
  OldDatum.payer    <-> NewDatum.parties.sender (second component)
  OldDatum.payee    <-> NewDatum.parties.recipient (first component)
  OldDatum.deadline <-> NewDatum.expires
  Claim(secret)    <-> Redeem(secret)
  Refund           <-> Cancel

Encodings also change tags, ordering, and nesting. Tests prove exact round trips
on the encoded domain, a related toy policy, and a counterexample for swapped roles.
No Mathlib dependency, Blaster tactic, sorry, or new axiom is required.
`Iso` is the small structure that Mathlib calls `Equiv`.
-/
namespace Equivalence.MappingExamples.Structural

open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)

structure Iso (A B : Type) where
  forward : A → B
  backward : B → A
  leftInv : ∀ a, backward (forward a) = a
  rightInv : ∀ b, forward (backward b) = b

def Iso.symm (e : Iso A B) : Iso B A :=
  ⟨e.backward, e.forward, e.rightInv, e.leftInv⟩

def Iso.trans (e : Iso A B) (f : Iso B C) : Iso A C where
  forward a := f.forward (e.forward a)
  backward c := e.backward (f.backward c)
  leftInv a := by simp only [f.leftInv, e.leftInv]
  rightInv c := by simp only [e.rightInv, f.rightInv]

structure Codec (A : Type) where
  encode : A → Data
  decode : Data → Option A
  decodeEncode : ∀ a, decode (encode a) = some a

/-- A bridge is partial on raw Data; unknown values are not silently rewritten. -/
def bridge (ca : Codec A) (cb : Codec B) (e : Iso A B) (d : Data) : Option Data :=
  (ca.decode d).map (fun a => cb.encode (e.forward a))

theorem bridge_encode (ca : Codec A) (cb : Codec B) (e : Iso A B) (a : A) :
    bridge ca cb e (ca.encode a) = some (cb.encode (e.forward a)) := by
  simp only [bridge, ca.decodeEncode, Option.map_some]

/-- Raw round trips on the entire *encoded image*, not on arbitrary Plutus Data. -/
theorem bridge_roundtrip (ca : Codec A) (cb : Codec B) (e : Iso A B) (a : A) :
    (bridge ca cb e (ca.encode a)).bind (bridge cb ca e.symm) = some (ca.encode a) := by
  simp only [bridge_encode, Option.bind_some, Iso.symm, e.leftInv]

/-- To cover every accepted raw value, a strict codec needs this additional law. -/
def Strict (c : Codec A) : Prop :=
  ∀ d a, c.decode d = some a → c.encode a = d

theorem bridge_roundtrip_on_decodable
    (ca : Codec A) (cb : Codec B) (e : Iso A B) (strictA : Strict ca)
    (d : Data) (a : A) (h : ca.decode d = some a) :
    (bridge ca cb e d).bind (bridge cb ca e.symm) = some d := by
  rw [← strictA d a h]
  exact bridge_roundtrip ca cb e a

structure OldDatum where
  payer : ByteString
  payee : ByteString
  deadline : Integer

structure NewDatum where
  expires : Integer
  parties : ByteString × ByteString -- recipient, sender

def datumIso : Iso OldDatum NewDatum where
  forward d := ⟨d.deadline, (d.payee, d.payer)⟩
  backward d := ⟨d.parties.2, d.parties.1, d.expires⟩
  leftInv d := by cases d; rfl
  rightInv d := by cases d with | mk t p => cases p; rfl

def oldCodec : Codec OldDatum where
  encode d := .Constr 0 [.B d.payer, .B d.payee, .I d.deadline]
  decode
    | .Constr 0 [.B payer, .B payee, .I deadline] => some ⟨payer, payee, deadline⟩
    | _ => none
  decodeEncode d := by cases d; rfl

def newCodec : Codec NewDatum where
  encode d := .Constr 7 [.I d.expires, .Constr 0 [.B d.parties.1, .B d.parties.2]]
  decode
    | .Constr 7 [.I expires, .Constr 0 [.B recipient, .B sender]] =>
        some ⟨expires, (recipient, sender)⟩
    | _ => none
  decodeEncode d := by cases d with | mk t p => cases p; rfl

theorem oldCodec_strict : Strict oldCodec := by
  intro d a h
  simp only [oldCodec] at h
  split at h <;> simp_all [oldCodec]
  subst a
  simp

theorem newCodec_strict : Strict newCodec := by
  intro d a h
  simp only [newCodec] at h
  split at h <;> simp_all [newCodec]
  subst a
  simp

/-- Encoding changes tag, field order, and nesting simultaneously. -/
theorem datum_wire_roundtrip (d : OldDatum) :
    (bridge oldCodec newCodec datumIso (oldCodec.encode d)).bind
      (bridge newCodec oldCodec datumIso.symm) = some (oldCodec.encode d) :=
  bridge_roundtrip oldCodec newCodec datumIso d

inductive OldAction where
  | claim : ByteString → OldAction
  | refund : OldAction

inductive NewAction where
  | cancel : NewAction
  | redeem : ByteString → NewAction

def actionIso : Iso OldAction NewAction where
  forward | .claim s => .redeem s | .refund => .cancel
  backward | .redeem s => .claim s | .cancel => .refund
  leftInv a := by cases a <;> rfl
  rightInv a := by cases a <;> rfl

def oldActionCodec : Codec OldAction where
  encode | .claim s => .Constr 0 [.B s] | .refund => .Constr 1 []
  decode
    | .Constr 0 [.B s] => some (.claim s)
    | .Constr 1 [] => some .refund
    | _ => none
  decodeEncode a := by cases a <;> rfl

def newActionCodec : Codec NewAction where
  encode | .cancel => .Constr 0 [] | .redeem s => .Constr 2 [.B s]
  decode
    | .Constr 0 [] => some .cancel
    | .Constr 2 [.B s] => some (.redeem s)
    | _ => none
  decodeEncode a := by cases a <;> rfl

theorem action_wire_roundtrip (a : OldAction) :
    (bridge oldActionCodec newActionCodec actionIso (oldActionCodec.encode a)).bind
      (bridge newActionCodec oldActionCodec actionIso.symm) =
        some (oldActionCodec.encode a) :=
  bridge_roundtrip oldActionCodec newActionCodec actionIso a

/-- A deliberately simplified typed policy, not a model of the repository's HTLC. -/
def oldAccept (d : OldDatum) (a : OldAction) (signer : ByteString) (now : Integer) : Prop :=
  match a with
  | .claim _ => signer = d.payee ∧ now < d.deadline
  | .refund => signer = d.payer ∧ d.deadline ≤ now

def newAccept (d : NewDatum) (a : NewAction) (signer : ByteString) (now : Integer) : Prop :=
  match a with
  | .redeem _ => signer = d.parties.1 ∧ now < d.expires
  | .cancel => signer = d.parties.2 ∧ d.expires ≤ now

theorem typed_policy_commutes (d : OldDatum) (a : OldAction) (s : ByteString) (t : Integer) :
    oldAccept d a s t ↔ newAccept (datumIso.forward d) (actionIso.forward a) s t := by
  cases a <;> rfl

/-- This alternative also has perfect inverse laws, but swaps the parties' roles. -/
def wrongRoleIso : Iso OldDatum NewDatum where
  forward d := ⟨d.deadline, (d.payer, d.payee)⟩
  backward d := ⟨d.parties.1, d.parties.2, d.expires⟩
  leftInv d := by cases d; rfl
  rightInv d := by cases d with | mk t p => cases p; rfl

theorem wrong_mapping_changes_acceptance :
    let d : OldDatum := ⟨"alice", "bob", 10⟩
    oldAccept d (.claim "secret") "bob" 0 ∧
      ¬ newAccept (wrongRoleIso.forward d) (.redeem "secret") "bob" 0 := by
  dsimp [oldAccept, newAccept, wrongRoleIso]
  decide

-- The bridge actually executes on the repository's Plutus Data representation.
#eval bridge oldCodec newCodec datumIso (oldCodec.encode ⟨"alice", "bob", 10⟩)
#eval bridge oldActionCodec newActionCodec actionIso (oldActionCodec.encode (.claim "secret"))

-- Verify the main proof artifacts do not depend on sorryAx or Blaster's blasterProven.
#print axioms datum_wire_roundtrip
#print axioms oldCodec_strict
#print axioms newCodec_strict
#print axioms action_wire_roundtrip
#print axioms typed_policy_commutes
#print axioms wrong_mapping_changes_acceptance

end Equivalence.MappingExamples.Structural
