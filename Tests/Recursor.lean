import CardanoLedgerApi.Recursors

import Blaster

namespace Tests.Recursor

set_option warn.sorry false

def findInt (x : Int) (inputs : List Int) : Option Int :=
  Recursor.find? y in inputs => y == x

def member (x : Int) (inputs : List Int) : Bool :=
  Recursor.any y in inputs => y == x

example (x : Int) (inputs : List Int) :
   member x inputs → (findInt x inputs).isSome := by
   induction inputs generalizing x <;> blaster

def mapTimesTwo (inputs : List Int) : List Int :=
  Recursor.map x in inputs with (2 : Int) * x

example (x : Int) (inputs : List Int) :
  member x inputs → member (2 * x) (mapTimesTwo inputs) := by
  induction inputs generalizing x <;> blaster


def findMapTwo (x : Int) (inputs : List Int) : Option Int :=
  Recursor.findMap? y in inputs => x == y with 2 * x

example (x : Int) (inputs : List Int) :
  member x inputs → findMapTwo x inputs = some (2 * x) := by
  induction inputs generalizing x <;> blaster

def allGeqTwo (inputs : List Int) : Bool :=
  Recursor.all x in inputs => x > (2 : Int)

def findAllGeqTwo (inputs : List Int) : List Int :=
  Recursor.findAll x in inputs => x > (2 : Int)

example (inputs : List Int) :
  allGeqTwo inputs → (findAllGeqTwo inputs) = inputs := by
  induction inputs <;> blaster

def anyGeqTwo (inputs : List Int) : Bool :=
  Recursor.any x in inputs => x > (2 : Int)

example (inputs : List Int) :
  anyGeqTwo inputs → ¬ (findAllGeqTwo inputs).isEmpty := by
  induction inputs <;> blaster

end Tests.Recursor
