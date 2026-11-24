# Detect a historical optimizer bug, then verify its fix

This tutorial compares three versions of a small Plutus V3 spending validator:

| File | Meaning |
| --- | --- |
| [`validator.uplc`](validator.uplc) | Original, handwritten UPLC |
| [`validator-buggy.uplc`](validator-buggy.uplc) | Actual output of the affected `uplc optimize` |
| [`validator-fixed.uplc`](validator-fixed.uplc) | Actual output after the upstream fix |

The bug is fixed upstream by [Plutus PR #8022](https://github.com/IntersectMBO/plutus/pull/8022).
Keeping the historical output lets us reproduce the negative test without
installing an old optimizer. The corrected output supplies the positive test.

## Build the checker

Install Git, Lean **4.24.0** through elan, and **Z3 5.4.0** with its `bin` directory
on `PATH`, as described in the repository's
[installation/test instructions](../../../../README.md#running-the-equivalence-tests).
Then run:

```sh
git clone https://github.com/input-output-hk/CardanoLedgerApiBlaster.git
cd CardanoLedgerApiBlaster
lake build uplc_equiv
```

Run the commands below from the repository root. The UPLC programs are checked in;
you do not need Nix, a Plinth compiler or the `uplc` executable to follow the tutorial.

## What the validator checks

The original validator reads an integer datum `d` from the spending context. It
computes the following strict expression, then returns unit:

```text
ifThenElse True 1 (divideInteger 1 (d - 1))
```

Consequently, it accepts integer datums other than `1`. Datum `1` causes division
by zero and rejection. A non-integer datum also causes rejection when decoded.
Datum `0` is an example of an accepted input.

UPLC applications evaluate their arguments before applying the function. The
builtin `ifThenElse` therefore receives already evaluated arguments: choosing its
first value does not prevent evaluation of the second value. Delayed branching
uses `delay`/`force`; see the separate
[`delayed-control`](../delayed-control.uplc) example.

The faulty constant-folding pass removed the possibly failing division. Its
output accepts a transaction with datum `1` that the original rejects. The fixed
pass preserves that evaluation. The generated files include transformations such
as `case`/`constr` and floated builtin forces; textual similarity is not the
criterion for equivalence.

## Find the incorrect optimization

```sh
tutorial_dir=equivalence/examples/uplc-optimize/tutorial
lake exe uplc_equiv \
  "$tutorial_dir/validator.uplc" "$tutorial_dir/validator-buggy.uplc" \
  --bounded --equivalence --steps 1000 \
  --max-inputs 1 --max-outputs 1 --max-signers 1 \
  --timeout 10 --wall-timeout 60
```

Expected verdict: **`bounded_inequivalent`**, exit status **1**. That nonzero
status means the checker successfully found a difference. The report includes:

```text
  acceptance_preserved: valid
  reverse_acceptance_preserved: falsified
Counterexample:
  Direction: NEW → OLD
  OLD: rejects (error)
  NEW: accepts (unit)
  Replay: confirmed
  Ledger validation: valid (ledger model)
```

One counterexample has `Datum: I 1`. The checker discovers the transaction context;
we do not supply its inputs, outputs or datum. It validates the context against
the ledger model and natively replays both scripts. Exact transaction fields can
vary; a malformed datum that the buggy program no longer decodes can also expose
the difference.

**Why `--equivalence` matters:** the default validator check is directional. It
requires NEW to accept everything OLD accepts, but permits additional acceptance.
Here OLD → NEW is valid; NEW → OLD exposes the incorrect optimization. Both
directions are required to check that an optimization preserves acceptance exactly.

## Verify the corrected optimization

Use the same original and the same comparison limits, changing only the output:

```sh
lake exe uplc_equiv \
  "$tutorial_dir/validator.uplc" "$tutorial_dir/validator-fixed.uplc" \
  --bounded --equivalence --steps 1000 \
  --max-inputs 1 --max-outputs 1 --max-signers 1 \
  --timeout 10 --wall-timeout 60
```

Expected verdict: **`bounded_equivalent`**, exit status **0**. Both acceptance
preservation queries are valid. The checker also confirms a concrete accepted
transaction by native replay; this is not a positive result obtained because
both scripts reject everything. There is no counterexample.

These small comparisons normally finish within a few seconds after the initial
build. A timeout or `inconclusive` result is not an equivalence proof. Add `--json`
to either command for machine-readable results, including `queries` and either the counterexample or the OLD-acceptance
status and witness, depending on the result.

## Exactly what was checked

The validator checks compare **acceptance**, not execution costs or arbitrary
return values. Successful V3 acceptance requires a unit result.

- `--bounded --steps 1000`: compare acceptance within 1,000 CEK execution steps;
  step exhaustion counts as nonacceptance in this mode.
- The context profile is a structured, ledger-model-valid **V3 spending** domain
  with a present datum and 0..1 transaction inputs, outputs and signer keys.
  The ledger-validity premise excludes invalid count combinations.
- Datum and redeemer remain symbolic, including their Data types. We use neither
  `--datum` nor `--redeemer` to restrict them.
- `--budget` is omitted: execution is uncosted, so this comparison does not claim
  equal execution units or equivalence at every on-chain budget threshold.
- The solver allowance is ten seconds per query; the complete check has a
  60-second wall-clock allowance.

The verdict applies to that declared domain and bound. It does not assert
unrestricted equivalence over every possible transaction. Verification uses
Blaster's SMT result, with native witness replay; the CLI does not reconstruct a
Lean proof term. See the [CLI documentation](../../../README.md)
for the remaining configuration and result meanings.

## The smallest integer-function example

The original historical reproducer is even smaller: `ifThenElse True 1 (1 / x)`.
To let Z3 find the failing integer directly:

```sh
lake exe uplc_equiv \
  equivalence/examples/uplc-optimize/ifthenelse.uplc \
  equivalence/examples/uplc-optimize/ifthenelseopt.uplc \
  --mode function --steps 1000 --timeout 10 --wall-timeout 60
```

Expected: **`inequivalent`**, exit status **1**, with input **0**. OLD fails and
NEW returns integer `1`. The historical output is simply a function returning `1`.

Then verify the fixed output:

```sh
lake exe uplc_equiv \
  equivalence/examples/uplc-optimize/ifthenelse.uplc \
  equivalence/examples/uplc-optimize/ifthenelse-fixed.uplc \
  --mode function --steps 1000 --timeout 10 --wall-timeout 60
```

Expected: **`equivalent`**, exit status **0**. Strict function mode compares both
returned constants and error outcomes for all integer inputs. Here `--steps` is
an analysis guard, since `--bounded` is omitted. Function mode ignores execution
costs by default. Unlike bounded validator preservation, strict function mode
already requests equality of outcomes and does not need `--equivalence`.

## Provenance and regeneration

Both output sets were generated with default optimizer options:

| Generator | Version | Exact revision |
| --- | --- | --- |
| Historical | `1.71.0.0` | `261766ad1d582bce8c86bad1af7a3b0e5355b21c` |
| Fixed, PR #8022 merge | `1.72.0.0` | `1ef5a0eef37772e35b1e587f7a3b0afa61be4358` |

[provenance.json](provenance.json) records source/output SHA-256 hashes, tool
versions, generator options and the upstream fix. Outputs were generated by the
actual executables, not edited to obtain the expected result.

Regeneration is optional. With Nix installed and flakes enabled:

```sh
tutorial_old_uplc=$(nix build --accept-flake-config --no-link --print-out-paths \
  github:IntersectMBO/plutus/261766ad1d582bce8c86bad1af7a3b0e5355b21c#uplc)
tutorial_fixed_uplc=$(nix build --accept-flake-config --no-link --print-out-paths \
  github:IntersectMBO/plutus/1ef5a0eef37772e35b1e587f7a3b0afa61be4358#uplc)
sh equivalence/examples/uplc-optimize/regenerate.sh "$tutorial_old_uplc/bin/uplc"
sh equivalence/examples/uplc-optimize/regenerate-fixed.sh "$tutorial_fixed_uplc/bin/uplc"
```

The scripts check the exact tool revision before writing files. A newer fixed
optimizer must not overwrite the historical faulty output. The first script also
regenerates the other historical regression fixtures in the parent directory.

`make check_equivalence` runs the checked-in regression tests, including both
comparisons and native acceptance checks at datums `0` and `1`. It requires Python
as described in the repository setup, but does not require either optimizer.
