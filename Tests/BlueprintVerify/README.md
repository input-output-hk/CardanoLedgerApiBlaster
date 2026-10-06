# Detached Auction assurance example

The Plutus `Example/Ual/Auction/FormalSpec.hs` module annotates imported script
and helper bindings. Its generator writes one blueprint script and a separate
assurance function registry. The reusable typed scenario constructors are in
`CardanoLedgerApi/Examples/Auction.lean`, adapted from upstream
`main` commit `9938562fd452351655fe2f6b63e583c62422687c`.
No upstream theorem or proof placeholder is imported by the example.

```sh
lake build Blaster:shared CardanoLedgerApi.Examples.Auction PlutusCore.UPLC.BlueprintEncoding.Assurance
lake env python3 Tests/BlueprintVerify/run_auction.py /path/to/example-ual-auction /path/to/run
```

Blaster must have a compatible Z3 in PATH. The newer local checkout requires
the `recfun-finder` simplifier; the runner pins the executable it actually finds.
The environment capture and checker both import the Auction model. Rebuilds or
a different solver require a fresh capture and regeneration of checking contexts.

The runner checks all 26 upstream theorem statements plus five interface and
scenario claims against the freshly compiled script. It exercises 18 concrete
executions and 13 negative checks, including counterexamples to the two upstream
"always fails" statements. Auction execution has an explicit 20,000 CEK-step
bound; this is not a ledger cost budget.

The typed contexts preserve the upstream examples, including scenarios with
non-ledger-valid values. These checks do not establish phase-one acceptance or
a complete security proof. Checking uses Blaster SMT without reconstruction
of a Lean kernel proof.

The runner loads Blaster's compiled shared library when it is available on the
Lake search path. An explicit `ASSURANCE_NATIVE_LIBRARY` overrides discovery;
the runner passes that same path to Lean's `--load-dynlib` and records its hash
in the checking environment. Capture and verification must use the same mode.
The manifest also pins the 60-second solver timeout, unlimited Lean heartbeats
and a recursion limit of 100000. The runner bounds each Lean process separately.
