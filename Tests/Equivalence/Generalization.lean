import Equivalence.Cli

namespace Tests.Equivalence.Generalization

open _root_.Equivalence

-- With default symbols the generalized entry points reproduce the original
-- argument builders for every case, mode and selection.
example (c : HTLC.Case) (mode selection : String) :
    HTLC.generalizedFamily c mode (Context.variationNames selection) {} = c.exploreArgs (mode == "htlc-claim") selection := by rfl
example (c : Vesting.Case) (mode selection : String) :
    Vesting.generalizedFamily c mode (Context.variationNames selection) {} = c.variedArgs (mode == "vesting-partial") selection := by rfl
example (c : Escrow.Case) (mode selection : String) :
    Escrow.generalizedFamily c mode (Context.variationNames selection) {} = c.args mode selection := by rfl

-- Baseline domains are independent of every newly quantified symbol.
example (c : HTLC.Case) (mode : String) (fields : Context.GeneralFields) :
    HTLC.generalizedFamily c mode ["baseline"] fields = HTLC.generalizedFamily c mode ["baseline"] {} := by rfl
example (c : Vesting.Case) (mode : String) (fields : Context.GeneralFields) :
    Vesting.generalizedFamily c mode ["baseline"] fields = Vesting.generalizedFamily c mode ["baseline"] {} := by rfl
example (c : Escrow.Case) (mode : String) (fields : Context.GeneralFields) :
    Escrow.generalizedFamily c mode ["baseline"] fields = Escrow.generalizedFamily c mode ["baseline"] {} := by rfl

end Tests.Equivalence.Generalization
