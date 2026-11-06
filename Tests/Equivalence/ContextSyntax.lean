import Equivalence.ValidContext

namespace Tests.Equivalence.ContextSyntax
open Lean Elab Command
open _root_.Equivalence
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)

-- Definitional equality alone is insufficient here: helper calls can preserve
-- values while changing Blaster's optimization path. Check the expanded syntax.
private def literalValue (ada : Int) (policy token : ByteString) (quantity : Int) : Data :=
  Data.Map [(.B "", .Map [(.B "", .I ada)]), (.B policy, .Map [(.B token, .I quantity)])]

private def macroValue (ada : Int) (policy token : ByteString) (quantity : Int) : Data :=
  context_value% ada policy token quantity

private def literalTxInfo (unused : Context.RawUnusedTxInfo) (inputs : List Data)
    (outputs : Data) (signers : List Data) (validRange : Data) : Data :=
  Data.Constr 0 [.List inputs, unused.referenceInputs, outputs, unused.fee,
    unused.mint, unused.certificates, unused.withdrawals, validRange,
    .List signers, unused.redeemers, unused.datums, unused.txId,
    unused.votes, unused.proposals, unused.treasury, unused.donation]

private def macroTxInfo (unused : Context.RawUnusedTxInfo) (inputs : List Data)
    (outputs : Data) (signers : List Data) (validRange : Data) : Data :=
  context_tx_info% unused inputs outputs signers validRange

private partial def stripMetadata : Expr → Expr
  | .mdata _ e => stripMetadata e
  | .app f a => .app (stripMetadata f) (stripMetadata a)
  | .lam n t b i => .lam n (stripMetadata t) (stripMetadata b) i
  | .forallE n t b i => .forallE n (stripMetadata t) (stripMetadata b) i
  | .letE n t v b d => .letE n (stripMetadata t) (stripMetadata v) (stripMetadata b) d
  | .proj n i e => .proj n i (stripMetadata e)
  | e => e

run_elab do
  for (actual, expected) in [( ``macroValue, ``literalValue), (``macroTxInfo, ``literalTxInfo)] do
    let actualBody := stripMetadata (← getConstInfo actual).value!
    let expectedBody := stripMetadata (← getConstInfo expected).value!
    unless actualBody.equal expectedBody do
      throwError "Macro expansion changed expression structure or binder names: {actual}"

private partial def listLength (e : Expr) : Nat :=
  if e.isAppOfArity ``List.nil 1 then 0
  else if e.isAppOfArity ``List.cons 3 then 1 + listLength e.getAppArgs[2]!
  else panic! "Expected a literal list spine"

private partial def leaves (e : Expr) : List Expr :=
  if e.isAppOfArity ``And 2 then leaves e.getAppArgs[0]! ++ leaves e.getAppArgs[1]!
  else [e]

run_elab do
  let type ← mkArrow (mkApp (mkConst ``List [.zero])
    (mkConst ``PlutusCore.UPLC.Term.Term)) (mkSort .zero)
  Meta.withLocalDeclD `p type fun p => do
    let goal ← ValidContext.proposition { maxInputs := 1, maxOutputs := 1, maxSigners := 1 } p
    let closed ← Meta.mkForallFVars #[p] goal
    unless !closed.hasFVar && !closed.hasMVar do throwError "Generated domain has free variables"
    Meta.forallTelescope goal fun vars body => do
      let names ← vars.toList.mapM fun var => return (← var.fvarId!.getDecl).userName
      for name in [`input0TxId, `input0Index, `output0Address, `output0Quantity, `signer0, `datum] do
        unless names.contains name do throwError "Missing model binder: {name}"
      let body ← Meta.zetaReduce body
      let counts := (leaves body).map fun leaf =>
        let args := leaf.getAppArgs.back!
        let fields := args.getAppArgs
        (listLength fields[1]!, listLength fields[2]!, listLength fields[3]!)
      unless counts == [(0,0,0), (0,0,1), (0,1,0), (0,1,1),
          (1,0,0), (1,0,1), (1,1,0), (1,1,1)] do
        throwError "Count cases or their order changed: {repr counts}"

end Tests.Equivalence.ContextSyntax
