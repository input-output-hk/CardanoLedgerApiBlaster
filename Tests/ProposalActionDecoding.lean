import CardanoLedgerApi.V3

open CardanoLedgerApi.V3.Contexts
open CardanoLedgerApi.V3.Governance
open PlutusCore.Data (Data)

private def proposal (action : Data) : ProposalProcedure :=
  ⟨12, .PubKeyCredential "", action⟩

example : validProposalActions [] = true := by decide
example : validProposalActions [proposal (Data.B "")] = false := by decide
example : validProposalActions [proposal (Data.Constr 6 [])] = true := by native_decide
