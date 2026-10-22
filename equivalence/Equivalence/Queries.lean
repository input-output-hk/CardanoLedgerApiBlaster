import Equivalence

namespace Equivalence.Queries

open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term (Term Program)
open PlutusCore.UPLC.Utils (fromFrameToInt)
open PlutusCore.Data (Data)
open PlutusCore.UPLC.CekValue (CekValue)

/-- Validator observations are acceptance/rejection, independent of the returned value. -/
def validatorValues (_ _ : CekValue) : Prop := True

/-- Three arbitrary Data arguments: datum, redeemer, and script context. -/
def dataArgs (datum redeemer context : Data) : List Term :=
  [.Const (.Data datum), .Const (.Data redeemer), .Const (.Data context)]

def validatorNoCompletedMismatch (left right : Program) (leftSteps rightSteps : Nat) : Prop :=
  ∀ datum redeemer context : Data, ¬ RunsMismatch validatorValues
    (execute left (dataArgs datum redeemer context) leftSteps)
    (execute right (dataArgs datum redeemer context) rightSteps)

def validatorTotalEquivalence (left right : Program) (leftSteps rightSteps : Nat) : Prop :=
  ∀ datum redeemer context : Data, RunsEquivalent validatorValues
    (execute left (dataArgs datum redeemer context) leftSteps)
    (execute right (dataArgs datum redeemer context) rightSteps)

def validatorSometimesOutput (program : Program) (steps : Nat) : Prop :=
  ∃ datum redeemer context : Data,
    PlutusCore.UPLC.Utils.isSuccessful (execute program (dataArgs datum redeemer context) steps)

/-- A V3 validator receives one Data argument containing the entire script context. -/
def contextArgs (context : Data) : List Term := [.Const (.Data context)]

def contextNoCompletedMismatch (left right : Program) (leftSteps rightSteps : Nat) : Prop :=
  ∀ context : Data, ¬ RunsMismatch validatorValues
    (execute left (contextArgs context) leftSteps)
    (execute right (contextArgs context) rightSteps)

def contextTotalEquivalence (left right : Program) (leftSteps rightSteps : Nat) : Prop :=
  ∀ context : Data, RunsEquivalent validatorValues
    (execute left (contextArgs context) leftSteps)
    (execute right (contextArgs context) rightSteps)

def contextSometimesOutput (program : Program) (steps : Nat) : Prop :=
  ∃ context : Data,
    PlutusCore.UPLC.Utils.isSuccessful (execute program (contextArgs context) steps)

/-- One parameterized validator input family, used to solve finite structural
    cases separately while retaining an unbounded integer parameter. -/
def familyNoCompletedMismatch (args : Int → List Term) (left right : Program)
    (leftSteps rightSteps : Nat) : Prop :=
  ∀ timestamp : Int, ¬ RunsMismatch validatorValues
    (execute left (args timestamp) leftSteps) (execute right (args timestamp) rightSteps)

def familyTotalEquivalence (args : Int → List Term) (left right : Program)
    (leftSteps rightSteps : Nat) : Prop :=
  ∀ timestamp : Int, RunsEquivalent validatorValues
    (execute left (args timestamp) leftSteps) (execute right (args timestamp) rightSteps)

def familySometimesOutput (args : Int → List Term) (program : Program) (steps : Nat) : Prop :=
  ∃ timestamp : Int, PlutusCore.UPLC.Utils.isSuccessful (execute program (args timestamp) steps)

def args (n : Integer) : List Term := [.Const (.Integer n)]

def sharedIntegerOutputs (left right : Program) (leftSteps rightSteps : Nat) : Prop :=
  ∀ n r1 r2 : Integer,
    fromFrameToInt (execute left (args n) leftSteps) = some r1 →
    fromFrameToInt (execute right (args n) rightSteps) = some r2 → r1 = r2

def noCompletedMismatch (left right : Program) (leftSteps rightSteps : Nat) : Prop :=
  ∀ n : Integer, ¬ RunsMismatch IntegerValues
    (execute left (args n) leftSteps) (execute right (args n) rightSteps)

def totalEquivalence (left right : Program) (leftSteps rightSteps : Nat) : Prop :=
  ∀ n : Integer, RunsEquivalent IntegerValues
    (execute left (args n) leftSteps) (execute right (args n) rightSteps)

def sometimesOutput (program : Program) (steps : Nat) : Prop :=
  ∃ n r : Integer, fromFrameToInt (execute program (args n) steps) = some r

end Equivalence.Queries
