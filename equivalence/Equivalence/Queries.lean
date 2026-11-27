import Equivalence.Acceptance
import Equivalence.Context
import Equivalence.Function

/-!
Defines the propositions submitted to the symbolic equivalence checker.
Expresses validator rejection and acceptance preservation over supplied arguments.
Adds strict and bounded function comparisons for integer, Data and Data-triple inputs.
-/

namespace Equivalence.Queries

open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term (Term Program)
open PlutusCore.Data (Data)

def dataArgs (datum redeemer context : Data) : List Term :=
  [.Const (.Data datum), .Const (.Data redeemer), .Const (.Data context)]

def contextArgs (context : Data) : List Term := [.Const (.Data context)]

def rejected (args : List Term) (old : Program) (cpu memory : Nat) (v3 : Bool)
    (bounded := false) (budgeted := true) (steps := 100000) : Prop :=
  Acceptance.accepts v3 (Function.executeValidator old args cpu memory v3 bounded budgeted steps) = some false

def contextRejected (old : Program) (cpu memory : Nat) (v3 : Bool)
    (bounded := false) (budgeted := true) (steps := 100000) : Prop :=
  ∀ context : Data, rejected (contextArgs context) old cpu memory v3 bounded budgeted steps

def validatorRejected (old : Program) (cpu memory : Nat) (v3 : Bool)
    (bounded := false) (budgeted := true) (steps := 100000) : Prop :=
  ∀ datum redeemer context : Data, rejected (dataArgs datum redeemer context) old cpu memory v3 bounded budgeted steps

def acceptancePreserved (args : List Term) (old new : Program)
    (cpu memory : Nat) (v3 : Bool)
    (bounded := false) (budgeted := true) (steps := 100000) : Prop :=
  Acceptance.Preserved v3 (Function.executeValidator old args cpu memory v3 bounded budgeted steps)
    (Function.executeValidator new args cpu memory v3 bounded budgeted steps)

def noAcceptanceRegression (args : List Term) (old new : Program)
    (cpu memory : Nat) (v3 : Bool)
    (bounded := false) (budgeted := true) (steps := 100000) : Prop :=
  ¬ Acceptance.Regression v3 (Function.executeValidator old args cpu memory v3 bounded budgeted steps)
    (Function.executeValidator new args cpu memory v3 bounded budgeted steps)

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

def spendingAcceptance (args : List Term) (program : Program) (cpu memory : Nat) (v3 bounded budgeted : Bool)
    (steps : Nat) : Option Bool :=
  Acceptance.accepts v3 (Function.executeValidator program (Context.spendingArguments v3 args)
    cpu memory v3 bounded budgeted steps)

def spendingRejected (args : List Term) (program : Program) (cpu memory : Nat) (v3 bounded budgeted : Bool)
    (steps : Nat) : Prop :=
  spendingAcceptance args program cpu memory v3 bounded budgeted steps = some false

def spendingAcceptancePreserved (args : List Term) (old new : Program) (cpu memory : Nat)
    (oldV3 newV3 bounded budgeted : Bool) (steps : Nat) : Prop :=
  spendingAcceptance args old cpu memory oldV3 bounded budgeted steps = some false ∨
    spendingAcceptance args new cpu memory newV3 bounded budgeted steps = some true

def spendingNoAcceptanceRegression (args : List Term) (old new : Program) (cpu memory : Nat)
    (oldV3 newV3 bounded budgeted : Bool) (steps : Nat) : Prop :=
  ¬ (spendingAcceptance args old cpu memory oldV3 bounded budgeted steps = some true ∧
    spendingAcceptance args new cpu memory newV3 bounded budgeted steps = some false)

def mintingAcceptance (args : List Term) (program : Program) (cpu memory : Nat) (v3 bounded budgeted : Bool)
    (steps : Nat) : Option Bool :=
  Acceptance.accepts v3 (Function.executeValidator program (Context.mintingArguments v3 args)
    cpu memory v3 bounded budgeted steps)

def mintingRejected (args : List Term) (program : Program) (cpu memory : Nat) (v3 bounded budgeted : Bool)
    (steps : Nat) : Prop :=
  mintingAcceptance args program cpu memory v3 bounded budgeted steps = some false

def mintingAcceptancePreserved (args : List Term) (old new : Program) (cpu memory : Nat)
    (oldV3 newV3 bounded budgeted : Bool) (steps : Nat) : Prop :=
  mintingAcceptance args old cpu memory oldV3 bounded budgeted steps = some false ∨
    mintingAcceptance args new cpu memory newV3 bounded budgeted steps = some true

def mintingNoAcceptanceRegression (args : List Term) (old new : Program) (cpu memory : Nat)
    (oldV3 newV3 bounded budgeted : Bool) (steps : Nat) : Prop :=
  ¬ (mintingAcceptance args old cpu memory oldV3 bounded budgeted steps = some true ∧
    mintingAcceptance args new cpu memory newV3 bounded budgeted steps = some false)

def withdrawalAcceptance (args : List Term) (program : Program) (cpu memory : Nat) (v3 bounded budgeted : Bool)
    (steps : Nat) : Option Bool :=
  Acceptance.accepts v3 (Function.executeValidator program (Context.withdrawalArguments v3 args)
    cpu memory v3 bounded budgeted steps)

def withdrawalRejected (args : List Term) (program : Program) (cpu memory : Nat) (v3 bounded budgeted : Bool)
    (steps : Nat) : Prop :=
  withdrawalAcceptance args program cpu memory v3 bounded budgeted steps = some false

def withdrawalAcceptancePreserved (args : List Term) (old new : Program) (cpu memory : Nat)
    (oldV3 newV3 bounded budgeted : Bool) (steps : Nat) : Prop :=
  withdrawalAcceptance args old cpu memory oldV3 bounded budgeted steps = some false ∨
    withdrawalAcceptance args new cpu memory newV3 bounded budgeted steps = some true

def withdrawalNoAcceptanceRegression (args : List Term) (old new : Program) (cpu memory : Nat)
    (oldV3 newV3 bounded budgeted : Bool) (steps : Nat) : Prop :=
  ¬ (withdrawalAcceptance args old cpu memory oldV3 bounded budgeted steps = some true ∧
    withdrawalAcceptance args new cpu memory newV3 bounded budgeted steps = some false)

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
