import Equivalence.Cli

namespace Tests.Equivalence.Generalization

open _root_.Equivalence

-- Baseline domains are independent of every newly quantified symbol.
example (c : HTLC.Case) (mode : String) (fields : Context.GeneralFields) :
    HTLC.generalizedFamily c mode ["baseline"] fields = HTLC.generalizedFamily c mode ["baseline"] {} := by rfl
example (c : Vesting.Case) (mode : String) (fields : Context.GeneralFields) :
    Vesting.generalizedFamily c mode ["baseline"] fields = Vesting.generalizedFamily c mode ["baseline"] {} := by rfl
example (c : Escrow.Case) (mode : String) (fields : Context.GeneralFields) :
    Escrow.generalizedFamily c mode ["baseline"] fields = Escrow.generalizedFamily c mode ["baseline"] {} := by rfl

end Tests.Equivalence.Generalization
