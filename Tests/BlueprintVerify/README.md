# Detached Auction assurance example

The Plutus `Example/Ual/Auction/FormalSpec.hs` module annotates imported script
and helper bindings. Its generator writes one blueprint script and a separate
assurance function registry. The scenario constructors are `PREDICATE` definitions
in the detached Haskell specification and are emitted into `assurance.json`.
The checker imports the general `CardanoLedgerApi.V3` library, not the handwritten
`Tests/BlueprintVerify/AuctionModel.lean` or any upstream theorem.

```sh
lake build Blaster:shared CardanoLedgerApi.V3 PlutusCore.UPLC.BlueprintEncoding.Assurance
lake env python3 Tests/BlueprintVerify/run_auction.py /path/to/example-ual-auction /path/to/run
```

Blaster must have a compatible Z3 in PATH. The newer local checkout requires
the `recfun-finder` simplifier; the runner pins the executable it actually finds.
The environment capture and checker both import the V3 ledger API. Rebuilds or
a different solver require a fresh capture and regeneration of checking contexts.

The runner checks all 26 upstream theorem statements plus five interface and
scenario claims against the freshly compiled script. It exercises 13 negative
checks, including counterexamples to the two upstream
"always fails" statements. Auction execution has an explicit 20,000 CEK-step
bound; this is not a ledger cost budget.

The emitted scenario contexts preserve the upstream examples, including scenarios
with non-ledger-valid values. These checks do not establish phase-one acceptance or
a complete security proof. Checking uses Blaster SMT without reconstruction
of a Lean kernel proof.

The runner loads Blaster's compiled shared library when it is available on the
Lake search path. An explicit `ASSURANCE_NATIVE_LIBRARY` overrides discovery;
the runner passes that same path to Lean's `--load-dynlib` and records its hash
in the checking environment. Capture and verification must use the same mode.
The manifest also pins the 60-second solver timeout, unlimited Lean heartbeats
and a recursion limit of 100000. The runner bounds each Lean process separately.

## Source-level ScriptContext counterexample

`CardanoLedgerApi.Counterexample.V3` supplies `ToCEX` codecs for V3 contexts,
transaction information and script information. They export the exact Plutus
Data encoding with a Haskell type hint. The Haskell decoder reconstructs the
source value, including fields kept as raw Data in the Lean model.

From the coordinated workspace, with the Plutus GHC 9.6.7 development environment
and its already-built Auction generator available:

```sh
lake build CardanoLedgerApi.Counterexample.V3 PlutusCore.UPLC.BlueprintEncoding.Assurance
lake env python3 Tests/BlueprintVerify/run_counterexample.py \
  --generator /absolute/path/to/example-ual-auction \
  --plutus /absolute/path/to/plutus \
  --source /absolute/path/to/plutus/doc/docusaurus/static/code/Example/Ual/Auction/FormalSpec.hs \
  --z3 /absolute/path/to/compatible/z3 \
  --output /absolute/path/to/auction-counterexample
```

The runner verifies the original `first_bid_exact` claim, then changes the
minimum bid from 100 to 101 in a copied annotation. It requires Blaster to find
inputs, native replay to falsify that instantiated property, and the compiled
Auction validator to halt. Call discovery follows specification helpers until
the digest-checked script wrapper, retaining the context before Data encoding.
The exported context must match the actual replayed argument exactly.

`ScriptContext.hs` contains a complete `V3.ScriptContext` reconstructed through
the real Haskell FromData instance. The runner compiles and runs it, requiring
`toData context` to reproduce the script argument. `counterexample.json` binds
the copied annotation, checked reports, generator and generated Haskell source;
`property-result.json` can be loaded in the local VS Code demo alongside the
copied `FormalSpec.hs`. The original correct Haskell source remains unchanged.

This demonstrates bounded script evaluation. It makes no phase-one transaction
validity, execution-cost or reconstructed Lean proof claim. Unknown source types,
failed codecs and unfinished CEK states do not become source-level witnesses.
