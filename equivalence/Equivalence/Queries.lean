import Equivalence.Acceptance
import Equivalence.Function
import Equivalence.Validator

namespace Equivalence.Queries

open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term (Term Program)
open PlutusCore.Data (Data)

def dataArgs (datum redeemer context : Data) : List Term :=
  [.Const (.Data datum), .Const (.Data redeemer), .Const (.Data context)]

def contextArgs (context : Data) : List Term := [.Const (.Data context)]

def rejected (args : List Term) (old : Program) (cpu memory : Nat) (v3 : Bool)
    (bounded := false) (budgeted := true) (steps := 100000) : Prop :=
  Acceptance.accepts v3 (Validator.execute old args cpu memory v3 bounded budgeted steps) = some false

def contextRejected (old : Program) (cpu memory : Nat) (v3 : Bool)
    (bounded := false) (budgeted := true) (steps := 100000) : Prop :=
  ∀ context : Data, rejected (contextArgs context) old cpu memory v3 bounded budgeted steps

def validatorRejected (old : Program) (cpu memory : Nat) (v3 : Bool)
    (bounded := false) (budgeted := true) (steps := 100000) : Prop :=
  ∀ datum redeemer context : Data, rejected (dataArgs datum redeemer context) old cpu memory v3 bounded budgeted steps

def acceptancePreserved (args : List Term) (old new : Program)
    (cpu memory : Nat) (v3 : Bool)
    (bounded := false) (budgeted := true) (steps := 100000) : Prop :=
  Acceptance.Preserved v3 (Validator.execute old args cpu memory v3 bounded budgeted steps)
    (Validator.execute new args cpu memory v3 bounded budgeted steps)

def noAcceptanceRegression (args : List Term) (old new : Program)
    (cpu memory : Nat) (v3 : Bool)
    (bounded := false) (budgeted := true) (steps := 100000) : Prop :=
  ¬ Acceptance.Regression v3 (Validator.execute old args cpu memory v3 bounded budgeted steps)
    (Validator.execute new args cpu memory v3 bounded budgeted steps)

def contextAcceptancePreserved (old new : Program) (cpu memory : Nat) (v3 : Bool)
    (bounded := false) (budgeted := true) (steps := 100000) : Prop :=
  ∀ context : Data, acceptancePreserved (contextArgs context) old new cpu memory v3 bounded budgeted steps

def contextNoAcceptanceRegression (old new : Program) (cpu memory : Nat) (v3 : Bool)
    (bounded := false) (budgeted := true) (steps := 100000) : Prop :=
  ∀ context : Data, noAcceptanceRegression (contextArgs context) old new cpu memory v3 bounded budgeted steps

def validatorAcceptancePreserved (old new : Program) (cpu memory : Nat) (v3 : Bool)
    (bounded := false) (budgeted := true) (steps := 100000) : Prop :=
  ∀ datum redeemer context : Data,
    acceptancePreserved (dataArgs datum redeemer context) old new cpu memory v3 bounded budgeted steps

def validatorNoAcceptanceRegression (old new : Program) (cpu memory : Nat) (v3 : Bool)
    (bounded := false) (budgeted := true) (steps := 100000) : Prop :=
  ∀ datum redeemer context : Data,
    noAcceptanceRegression (dataArgs datum redeemer context) old new cpu memory v3 bounded budgeted steps

def args (n : Integer) : List Term := [.Const (.Integer n)]

def integerRejected (old : Program) (cpu memory : Nat) (v3 : Bool)
    (bounded := false) (budgeted := true) (steps := 100000) : Prop :=
  ∀ n : Integer, rejected (args n) old cpu memory v3 bounded budgeted steps

def integerAcceptancePreserved (old new : Program) (cpu memory : Nat) (v3 : Bool)
    (bounded := false) (budgeted := true) (steps := 100000) : Prop :=
  ∀ n : Integer, acceptancePreserved (args n) old new cpu memory v3 bounded budgeted steps

def integerNoAcceptanceRegression (old new : Program) (cpu memory : Nat) (v3 : Bool)
    (bounded := false) (budgeted := true) (steps := 100000) : Prop :=
  ∀ n : Integer, noAcceptanceRegression (args n) old new cpu memory v3 bounded budgeted steps

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
