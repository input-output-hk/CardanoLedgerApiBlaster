# Cross-compiler counterexample: historical two-party escrow

Compare the preserved Scalus and Plinth implementations of the earlier
UPLC-CAPE two-party escrow scenario:

```sh
lake exe uplc_equiv \
  equivalence/examples/two_party_escrow_old/Scalus_0.18.2_Unisay.cbor_hex \
  equivalence/examples/two_party_escrow_old/Plinth_1.67.0.0_Unisay.cbor_hex \
  --bounded --max-inputs 1 --max-outputs 1
```

Run this from the repository root after following the
[build instructions](../../../README.md#running-the-equivalence-tests).
The checked-in CBOR-hex programs are sufficient; Scalus and Plinth do not need
to be installed. `lake exe` builds the CLI if necessary.

## What the checker discovers

Expected verdict: **`bounded_regression`**, exit status **1**. This is a successful
counterexample detection, not a tool error. The first script is OLD and the
second is NEW, so the report shows:

```text
  acceptance_preserved: falsified
Counterexample:
  Direction: OLD → NEW
  OLD: accepts (unit)
  NEW: rejects (error)
  Replay: confirmed
  Ledger validation: valid (ledger model)
```

The solver chooses the datum, redeemer and transaction fields. The command
supplies neither a complete input nor a fixed datum, redeemer or ADA amount, and
does not use `--split-dispatch`.

A reference run found:

| Field | Discovered value |
| --- | --- |
| Redeemer | `I 1` |
| Spending input ADA | 75,025,513 lovelace |
| Output ADA | **75,000,000 lovelace (75 ADA)** |
| Transaction fee | 25,513 lovelace |

The ADA amounts balance: input = output + fee. Both scripts are executed again
on the concrete model, and its ledger-model validity is checked independently.
The complete, readable context is printed in the report. Exact datum payloads,
fees, references, signers and other fields can vary between solver runs; the
example illustrates symbolic discovery rather than a fixed transaction template.

In particular, **75,000,000 is not supplied to the checker**. It emerges from
solving the comparison of the two scripts.

## Comparison scope and defaults

This command uses validator mode and the structured, ledger-model-valid V3
spending-context domain. OLD acceptance must imply NEW acceptance. A single
replayed violation establishes the reported directional regression; checking
both directions with `--equivalence` is unnecessary for this counterexample.

The two explicit count limits include 0..1 transaction inputs and outputs. Ledger
validity excludes invalid combinations, including spending without a matching
input. Datum and redeemer are symbolic Data values, not limited to a list of
handpicked examples. Other options keep their defaults:

- Up to **two signer keys**.
- An execution bound of **100,000 CEK steps**, because `--bounded` makes the step
  limit part of the comparison scope. Execution is uncosted without `--budget`.
- A **20-second Z3 deadline per query** and **180-second overall wall deadline**.

This is a bounded acceptance difference in the declared model, not a claim of
unrestricted equivalence or on-chain reachability of the transaction. The
reference development run completed in about four seconds; performance depends
on the machine, solver and checker revisions. A timeout is `inconclusive`, not
evidence that the scripts agree. For a longer attempt, append:

```sh
--timeout 100 --wall-timeout 500
```

Add `--json` to obtain the machine-readable counterexample, including
`counterexample.replayed`, `counterexample.ledger_validity`, and both acceptance
outcomes. See the [CLI reference](../../README.md)
for all options and verdict meanings.

## Why these historical files?

The `_old` directory preserves the earlier scenario and its compiled submissions.
The current `two_party_escrow` example represents a revised scenario. Substituting
that directory changes the comparison and need not reproduce this difference.

The Scalus and Plinth submissions are independently written implementations.
Their disagreement is evidence of different behavior; it does **not**, by itself,
show that either compiler mistranslated its source, or identify which source
satisfies the intended specification. The historical
[source comparison](../../benchmarks/results/2026-11-05-native-limits/source-comparison.json)
records differences in their validation checks.

For an actual incorrect optimization, with original, faulty and corrected outputs
and a verified positive comparison, follow the
[optimizer regression tutorial](../uplc-optimize/tutorial/README.md).
