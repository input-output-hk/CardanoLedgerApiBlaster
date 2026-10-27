import Equivalence.Acceptance
import Equivalence.Function

namespace Equivalence.Queries

open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term (Term Program)
open PlutusCore.Data (Data)

def dataArgs (datum redeemer context : Data) : List Term :=
  [.Const (.Data datum), .Const (.Data redeemer), .Const (.Data context)]

def contextArgs (context : Data) : List Term := [.Const (.Data context)]

def rejected (args : List Term) (old : Program) (cpu memory : Nat) (v3 : Bool) : Prop :=
  Acceptance.accepts v3 (Acceptance.execute old args cpu memory v3) = some false

def contextRejected (old : Program) (cpu memory : Nat) (v3 : Bool) : Prop :=
  ∀ context : Data, rejected (contextArgs context) old cpu memory v3

def validatorRejected (old : Program) (cpu memory : Nat) (v3 : Bool) : Prop :=
  ∀ datum redeemer context : Data, rejected (dataArgs datum redeemer context) old cpu memory v3

def acceptancePreserved (args : List Term) (old new : Program)
    (cpu memory : Nat) (v3 : Bool) : Prop :=
  Acceptance.Preserved v3 (Acceptance.execute old args cpu memory v3)
    (Acceptance.execute new args cpu memory v3)

def noAcceptanceRegression (args : List Term) (old new : Program)
    (cpu memory : Nat) (v3 : Bool) : Prop :=
  ¬ Acceptance.Regression v3 (Acceptance.execute old args cpu memory v3)
    (Acceptance.execute new args cpu memory v3)

def contextAcceptancePreserved (old new : Program) (cpu memory : Nat) (v3 : Bool) : Prop :=
  ∀ context : Data, acceptancePreserved (contextArgs context) old new cpu memory v3

def contextNoAcceptanceRegression (old new : Program) (cpu memory : Nat) (v3 : Bool) : Prop :=
  ∀ context : Data, noAcceptanceRegression (contextArgs context) old new cpu memory v3

def validatorAcceptancePreserved (old new : Program) (cpu memory : Nat) (v3 : Bool) : Prop :=
  ∀ datum redeemer context : Data,
    acceptancePreserved (dataArgs datum redeemer context) old new cpu memory v3

def validatorNoAcceptanceRegression (old new : Program) (cpu memory : Nat) (v3 : Bool) : Prop :=
  ∀ datum redeemer context : Data,
    noAcceptanceRegression (dataArgs datum redeemer context) old new cpu memory v3

def args (n : Integer) : List Term := [.Const (.Integer n)]

def integerRejected (old : Program) (cpu memory : Nat) (v3 : Bool) : Prop :=
  ∀ n : Integer, rejected (args n) old cpu memory v3

def integerAcceptancePreserved (old new : Program) (cpu memory : Nat) (v3 : Bool) : Prop :=
  ∀ n : Integer, acceptancePreserved (args n) old new cpu memory v3

def integerNoAcceptanceRegression (old new : Program) (cpu memory : Nat) (v3 : Bool) : Prop :=
  ∀ n : Integer, noAcceptanceRegression (args n) old new cpu memory v3

def functionEquivalent (args : List Term) (old new : Program) (cpu memory : Nat)
    (v3 budgeted : Bool) (steps : Nat) : Prop :=
  old = new ∨ Function.same (Function.execute old args cpu memory v3 budgeted steps)
    (Function.execute new args cpu memory v3 budgeted steps) = some true

def integerFunctionEquivalent (old new : Program) (cpu memory : Nat)
    (v3 budgeted : Bool) (steps : Nat) : Prop :=
  ∀ n : Integer, functionEquivalent (args n) old new cpu memory v3 budgeted steps

def dataFunctionEquivalent (old new : Program) (cpu memory : Nat)
    (v3 budgeted : Bool) (steps : Nat) : Prop :=
  ∀ input : Data, functionEquivalent (contextArgs input) old new cpu memory v3 budgeted steps

def data3FunctionEquivalent (old new : Program) (cpu memory : Nat)
    (v3 budgeted : Bool) (steps : Nat) : Prop :=
  ∀ datum redeemer context : Data,
    functionEquivalent (dataArgs datum redeemer context) old new cpu memory v3 budgeted steps

def boundedFunctionEquivalent (args : List Term) (old new : Program) (cpu memory : Nat)
    (v3 budgeted : Bool) (steps : Nat) : Prop :=
  old = new ∨ Function.boundedSame (Function.execute old args cpu memory v3 budgeted steps)
    (Function.execute new args cpu memory v3 budgeted steps) = true

def integerBoundedFunctionEquivalent (old new : Program) (cpu memory : Nat)
    (v3 budgeted : Bool) (steps : Nat) : Prop :=
  ∀ n : Integer, boundedFunctionEquivalent (args n) old new cpu memory v3 budgeted steps

def dataBoundedFunctionEquivalent (old new : Program) (cpu memory : Nat)
    (v3 budgeted : Bool) (steps : Nat) : Prop :=
  ∀ input : Data, boundedFunctionEquivalent (contextArgs input) old new cpu memory v3 budgeted steps

def data3BoundedFunctionEquivalent (old new : Program) (cpu memory : Nat)
    (v3 budgeted : Bool) (steps : Nat) : Prop :=
  ∀ datum redeemer context : Data,
    boundedFunctionEquivalent (dataArgs datum redeemer context) old new cpu memory v3 budgeted steps

def boundedFunctionPreserved (args : List Term) (old new : Program) (cpu memory : Nat)
    (v3 budgeted : Bool) (steps : Nat) : Prop :=
  old = new ∨ Function.boundedPreserved (Function.execute old args cpu memory v3 budgeted steps)
    (Function.execute new args cpu memory v3 budgeted steps) = true

def integerBoundedFunctionPreserved (old new : Program) (cpu memory : Nat)
    (v3 budgeted : Bool) (steps : Nat) : Prop :=
  ∀ n : Integer, boundedFunctionPreserved (args n) old new cpu memory v3 budgeted steps

def dataBoundedFunctionPreserved (old new : Program) (cpu memory : Nat)
    (v3 budgeted : Bool) (steps : Nat) : Prop :=
  ∀ input : Data, boundedFunctionPreserved (contextArgs input) old new cpu memory v3 budgeted steps

def data3BoundedFunctionPreserved (old new : Program) (cpu memory : Nat)
    (v3 budgeted : Bool) (steps : Nat) : Prop :=
  ∀ datum redeemer context : Data,
    boundedFunctionPreserved (dataArgs datum redeemer context) old new cpu memory v3 budgeted steps

end Equivalence.Queries
