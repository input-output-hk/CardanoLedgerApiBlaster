import Equivalence.Acceptance

namespace Equivalence.Queries

open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.Term (Term Program)
open PlutusCore.Data (Data)

def dataArgs (datum redeemer context : Data) : List Term :=
  [.Const (.Data datum), .Const (.Data redeemer), .Const (.Data context)]

def contextArgs (context : Data) : List Term := [.Const (.Data context)]

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

def integerAcceptancePreserved (old new : Program) (cpu memory : Nat) (v3 : Bool) : Prop :=
  ∀ n : Integer, acceptancePreserved (args n) old new cpu memory v3

def integerNoAcceptanceRegression (old new : Program) (cpu memory : Nat) (v3 : Bool) : Prop :=
  ∀ n : Integer, noAcceptanceRegression (args n) old new cpu memory v3

end Equivalence.Queries
