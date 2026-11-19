# UPLC example corpus benchmarks

Run the collected UPLC examples through the checker library in isolated native
workers. The runner deduplicates identical binaries, preserves their file aliases,
and compares each distinct binary with a different implementation in its scenario.
It records preprocessing time, CPU time, peak RSS, phase events and checker reports,
with results grouped by scenario.

Use the Lean and Z3 prerequisites described in the repository README. On Linux
or macOS, run from the repository root:

```sh
lake build equivalence_benchmark_worker
python3 -m unittest discover -s equivalence/benchmarks -p test_corpus.py
python3 equivalence/benchmarks/corpus.py \
  --output equivalence/benchmarks/local-runs/corpus-baseline
```

The output directory must be new. `local-runs/` is ignored; do not commit routine
raw outputs or saved executable binaries.

## Workload and limits

The default screen uses 5,000 uncosted execution steps, a one-second solver limit
and a five-second external wall deadline per comparison. Cases run sequentially.
Each worker owns a process session; the watchdog terminates its solver children
as well as the worker when the deadline expires.

Validators check directional bounded acceptance preservation over symbolic V3
spending contexts with maxima 1 transaction input, 1 output and 1 signer. Datum
and redeemer remain symbolic. OLD rejection is skipped; the checker still needs
acceptance evidence before reporting preservation.

Functions check directional bounded result preservation for an arbitrary integer.
ECD uses an explicit slice, `gcd(x, 462)`, through an in-memory adapter; the second
integer is fixed rather than independently symbolic. Check expected GCD values
on every ECD fixture and its adapter with:

```sh
lake env lean equivalence/benchmarks/verify_corpus_ecd.lean
```

Change measurement limits or select cases with:

```sh
python3 equivalence/benchmarks/corpus.py \
  --output equivalence/benchmarks/local-runs/selected \
  --wall-timeout 20 --steps 5000 --solver-timeout 5 \
  --case htlc--Plinth_1.65.0.0_Unisay
```

`--case` is repeatable. `--binary PATH` selects a saved native benchmark worker.
The files in `equivalence/examples` are the input corpus; no external UPLC-CAPE
checkout or historical benchmark scripts are required.

## Reproducible comparisons

Each run writes `corpus.json` with aliases, pairing and binary hashes. Reuse that
manifest to freeze the workload and reject changed fixture bytes:

```sh
python3 equivalence/benchmarks/corpus.py \
  --manifest equivalence/benchmarks/local-runs/corpus-baseline/corpus.json \
  --output equivalence/benchmarks/local-runs/corpus-candidate
python3 equivalence/benchmarks/compare_corpus.py \
  equivalence/benchmarks/local-runs/corpus-baseline/results.json \
  equivalence/benchmarks/local-runs/corpus-candidate/results.json \
  --output equivalence/benchmarks/local-runs/comparison.json
```

Keep step, solver and wall limits the same when comparing builds. Receipts record
native worker and helper hashes, dependency revisions/diffs and selected cases.
The output also contains per-case raw reports and phase logs, `results.json` and
scenario aggregates in `groups.json`.

Preprocessing time includes checker environment setup and all preprocessing
phases. Peak RSS comes from per-worker `wait4` accounting, including descendants
accounted by the OS through waited child usage; it is not peak aggregate RSS of
the complete process tree. A previous worker's peak is never reused for a later
case.

Speed and memory ratios include only cases completed on both builds with matching
verdict/query labels. Timeouts, errors and changed outcomes are reported separately.
A smaller RSS at the same timeout can mean less completed work, so it is not
automatically a memory improvement. Equal inconclusive labels do not establish
semantic equivalence. Report scenarios separately and repeat promising cases in
interleaved order rather than treating compiler versions as independent programs.

## Initial baseline

The [initial corpus screen and cache experiment](results/2026-11-19-corpus-cache-screen/SUMMARY.md)
cover 122 files as 88 distinct binaries across nine scenario groups. The retained
results include known upstream decoder/SMT limitations and seven-case ABBA
repeats. The experimental cache change was reverted; it is retained only as an
artifact for reproducing the measurement.
