import Equivalence.ValidContext
import Blaster

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Tests.Equivalence.ValidContextProofs
open _root_.Equivalence
open PlutusCore.UPLC.Term (Term)
open PlutusCore.UPLC.PlutusScript (PlutusScript)

#import_uplc htlcOld PlutusV3 single_cbor_hex "equivalence/examples/htlc/Plinth_1.65.0.0_Unisay.cbor_hex"
#import_uplc htlcNew PlutusV3 single_cbor_hex "equivalence/examples/htlc/Plinth_1.67.0.0_Unisay.cbor_hex"
#import_uplc vestingOld PlutusV3 single_cbor_hex "equivalence/examples/linear_vesting/Plinth_1.65.0.0_Unisay.cbor_hex"
#import_uplc vestingNew PlutusV3 single_cbor_hex "equivalence/examples/linear_vesting/Plinth_1.67.0.0_Unisay.cbor_hex"
#import_uplc escrowOld PlutusV3 single_cbor_hex "equivalence/examples/two_party_escrow/Plinth_1.65.0.0_Unisay.cbor_hex"
#import_uplc escrowNew PlutusV3 single_cbor_hex "equivalence/examples/two_party_escrow/Plinth_1.67.0.0_Unisay.cbor_hex"

def accepts (script : PlutusScript) (args : List Term) (budgeted : Bool) : Option Bool :=
  Acceptance.accepts true (Function.execute script.script args
    10000000000 14000000 true budgeted 5000)

/-- Both executions must finish within the analysis guard. -/
def completed (old new : PlutusScript) (budgeted : Bool) (args : List Term) : Prop :=
  accepts old args budgeted = accepts new args budgeted ∧ accepts old args budgeted ≠ none

-- Default maxima: 0..2 inputs, outputs and signers. These stronger checks also
-- establish completion within 5,000 steps, without execution-unit accounting.
#blaster (timeout: 30) (reconstruct-proofs: 0)
  [valid_context% 2 2 2 (completed htlcOld htlcNew false)]
#blaster (timeout: 30) (reconstruct-proofs: 0)
  [valid_context% 2 2 2 (completed vestingOld vestingNew false)]
#blaster (timeout: 30) (reconstruct-proofs: 0)
  [valid_context% 2 2 2 (completed escrowOld escrowNew false)]

end Tests.Equivalence.ValidContextProofs
