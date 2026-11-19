# Example corpus baseline and a local-cache sizing experiment

The available examples provide a useful basic regression corpus. This run covers
all 122 collected files as 88 distinct binary cases across nine scenario groups
and six compiler families. Each distinct binary is compared with a different
binary in its own scenario. Aliases are retained rather than counted as
independent workloads; results are grouped by scenario rather than pooled across
the uneven collection of compiler versions.

The first cache experiment does **not** justify changing the default. Using the
hash map's default initial capacity of eight instead of 256 for local rewrite
maps gives repeatable peak-RSS reductions of roughly 2–3% on three selected
completed validator comparisons. It does not show a convincing general speedup.
The initial arithmetic slowdowns largely disappear in interleaved repeats.
The optimizer source and normal binaries are restored; only benchmark tools,
results and the experimental patch remain.

## Corpus and workload

| Scenario | Files | Distinct binary cases |
|---|---:|---:|
| ECD | 7 | 4 |
| Factorial | 6 | 3 |
| Naive factorial | 18 | 9 |
| Fibonacci | 23 | 13 |
| Naive Fibonacci | 18 | 10 |
| HTLC | 15 | 14 |
| Linear vesting | 13 | 13 |
| Replacement escrow | 12 | 12 |
| Old escrow | 10 | 10 |
| **Total** | **122** | **88** |

Compiler families are Aiken, OpShin, Pebble, Plinth, Plutarch and Scalus. This is
a basic collection of example programs, not 88 independent real-world scenarios.
Old and new escrow are separate groups because the scenario changed substantially.

The common per-case limits are 5,000 uncosted execution steps, a one-second Z3
deadline, seed zero and a five-second external wall deadline. Validators use
directional bounded acceptance preservation over symbolic structured V3 contexts
with maxima 1 input / 1 output / 1 signer. Datum and redeemer remain symbolic.
Deferred OLD rejection is skipped, but acceptance evidence is still required by
the checker before reporting preservation. Functions use directional bounded
result preservation for an arbitrary integer.

ECD needs two integers. Its explicit measured slice is **gcd(x, 462)**, with
arbitrary integer x, using an in-memory UPLC adapter on both sides. It is not a
comparison for two independently symbolic inputs. The adapter is checked against
the original two-argument execution at five concrete inputs on each worker run.
An additional expected-value check verifies that all seven ECD files and their
adapters actually return the expected integer GCD for -12, 0, 6, 48 and 1071:
**35 expected-value checks pass**. Agreement on two evaluation errors would not
pass that additional check.

The unary integer interface is also checked natively on all 65 factorial and
Fibonacci fixture files at inputs 0, 1 and 5: **all 195 observations return an
integer**. This is an interface/replay check, not a proof that those functions
agree on every input. `integer-input-replay.json` retains the actual values,
including for comparisons blocked by SMT translation.

The native benchmark worker calls the normal checker library. A separate Python
watchdog owns its process session, kills the worker and any solver children at
the wall deadline, and records phase events as they arrive. Preprocessing time
includes the checker's environment setup and all reported preprocessing phases;
it is not a timer around only the inner optimizer. Polling granularity is 20 ms.

Memory is per-worker OS `wait4` maximum RSS, including any descendants the OS
accounts through waited child usage. It is **not aggregate simultaneous RSS** of
the complete process tree and is not a live-object census. This accounting was
validated with a child allocating 100 MiB; each case gets its own usage record,
so earlier workers' peaks cannot become later cases' measurements.

## Baseline and candidate screens

The baseline takes 355.8 seconds across all cases. It records:

- 15 `bounded_preserved` results.
- 65 inconclusive results, including 51 wall timeouts, 50 during preprocessing.
- Eight tool errors: five comparisons encounter unsupported `BitVec` instance
  parameters and three fail program decoding. `known-errors.json` lists the
  actual pairs and messages; an error in a pair does not by itself identify the
  left script as its cause. These are existing coverage gaps, not successes.

The candidate changes exactly one line in pinned Blaster
`Blaster/Optimize/Env/Types.lean`: local rewrite maps use
`HashMap.emptyWithCapacity` (default eight), replacing an explicit capacity of
256. Visited-set sizing, cache lifetime, hash algorithms, solver settings and
checker semantics are unchanged. `candidate.patch` preserves that experiment.

The same runner, worker source, frozen pairings and fixture bytes are used for
both screens. The candidate has 14 bounded-preservation results, 66 inconclusive
results and the same eight errors. One formerly completed Fibonacci comparison
crosses the five-second wall cutoff; no newly reported counterexample appears.

Only 28 cases complete on **both** sides without an error and with matching
verdict/query labels. Ratios below use only those cases; `+` means an increase
under the candidate. Compiler versions are summarized within their scenario.

| Scenario | Comparable cases | Median preprocessing change | Median peak RSS change |
|---|---:|---:|---:|
| Naive factorial | 6 | +8.1% | +0.5% |
| Fibonacci | 4 | +7.7% | +0.3% |
| Naive Fibonacci | 4 | +3.6% | +1.1% |
| HTLC | 7 | +0.5% | -2.6% |
| Linear vesting | 4 | +2.4% | -3.1% |
| Old escrow | 3 | -0.5% | -2.4% |
| ECD, factorial, replacement escrow | 0 | Censored / errors | Censored / errors |

These are single-pass screen observations. The initial +4–8% arithmetic timing
differences must not be promoted to stable regression claims: the repeats below
do not reproduce them at that size. The candidate also often has lower RSS on
cases still preprocessing at five seconds, but those are not fixed-work memory
comparisons. A slower expansion can produce a smaller heap at the same wall
deadline. Those censored cases are retained as observations and excluded from
the ratios.

## Interleaved repeats

Seven cases are repeated in **A/B/B/A** order using saved native workers built
from the original and candidate sources. Deadlines are increased to ten seconds.
There are two observations per variant per case; all 28 runs finish within the
deadline and have matching verdict and query labels within each case. These
remain exploratory repetitions, not confidence intervals or proof that
inconclusive outcomes have equal semantics.

| Case | Median preprocessing change | Median peak RSS change |
|---|---:|---:|
| Naive factorial / OpShin 0.26.1 | +0.5% | -0.3% |
| Fibonacci / Plinth 1.45 | +0.9% | +0.8% |
| Fibonacci / Plinth 1.61 (cutoff control) | +1.6% | -0.9% |
| Naive Fibonacci / Plinth 1.45 | -0.3% | +1.1% |
| HTLC / Plinth 1.65 | +3.1% | -2.5% |
| Linear vesting / Plinth 1.64 | -0.9% | -3.1% |
| Old escrow / Plinth 1.65 | +2.4% | -2.2% |

The cutoff-control Fibonacci comparison establishes bounded preservation on all
four runs with the longer deadline. Its median preprocessing times are 4.941
seconds for A and 5.019 for B, demonstrating why a five-second screen alone is
not a reliable classifier of that performance difference. Total elapsed time
also contains startup and other phases.

The first invocation of each saved executable has a longer startup in these
repeats (about 1.3 seconds versus about 0.2 seconds on later invocations).
Reported ratios compare preprocessing phases, not total process wall times.
The saved original worker reproduces the larger validator RSS while the candidate
reproduces the smaller RSS; the measurements are taken with normal dependency
sources and domain/model build artifacts restored. The cache-construction change
is compiled into the saved native workers. Binary and source hashes are recorded.

The measured memory tradeoff may be useful, but this is insufficient evidence
for a general performance improvement. No cache default is changed as a result.
The new corpus can now be reused to assess expression/context lifecycle changes
or other optimizations, with longer or fixed-work measurements for censored cases.

## Tools, checks and retained evidence

- `equivalence/benchmarks/CorpusWorker.lean` and the optional
  `equivalence_benchmark_worker` Lake target isolate the checker library.
- `equivalence/benchmarks/corpus.py` inventories aliases, selects nonidentical
  within-scenario pairs, runs each in an owned session and records per-worker
  phase, CPU, RSS, timeout and report data. `--manifest` freezes the workload.
- `equivalence/benchmarks/compare_corpus.py` rejects different case sets/requests
  and excludes censored, error and changed-outcome cases from speed ratios.
- Four tests pass for complete fixture coverage, nonidentical pairing,
  phase/resource recording, worker/solver process-group cleanup and comparison
  censoring. All 35 ECD expected-value checks pass.
- The final normal `uplc_equiv` and benchmark worker build succeeds. Blaster's
  working tree is clean; its edited file is restored byte-for-byte and the normal
  benchmark worker matches the original binary hash (`restoration.json`).

`corpus.json` records all aliases, selected paths, decoded-file hashes and
pairings. `baseline.json`, `candidate.json`, their group summaries and provenance
files retain the screens. `comparison.json` retains the per-case ratios and
transitions. `confirmation.json` retains all 28 repeats, exact commands, binary
receipts, samples and medians. `provenance.json` records helper hashes and raw
output locations; the raw per-case stdout/stderr and saved native binaries remain
in ignored `local-runs/` directories. This adds no per-case raw folders to the
tracked benchmark collection.

## Reproduction

From the repository root, with the normal dependencies and toolchain installed:

```sh
lake build equivalence_benchmark_worker
python3 -m unittest discover -s equivalence/benchmarks -p test_corpus.py
lake env lean equivalence/benchmarks/verify_corpus_ecd.lean
python3 equivalence/benchmarks/corpus.py \
  --output equivalence/benchmarks/local-runs/corpus-baseline
```

The runner discovers the examples by default. To replay these exact pairings
and reject changed fixture bytes, add:

```sh
--manifest equivalence/benchmarks/results/2026-11-19-corpus-cache-screen/corpus.json
```

For another build, pass that native worker with `--binary`; repeat `--case ID`
to select comparisons and use `--wall-timeout 10` for longer controls. Run cases
sequentially and keep binary/source receipts. Compare two runs with:

```sh
python3 equivalence/benchmarks/compare_corpus.py \
  equivalence/benchmarks/local-runs/corpus-baseline/results.json \
  equivalence/benchmarks/local-runs/corpus-candidate/results.json \
  --output equivalence/benchmarks/local-runs/corpus-comparison.json
```

`candidate.patch` is a temporary dependency experiment, not a retained source
change. Reproducing it requires rebuilding the worker after applying it, and
restoring the original dependency source and rebuilding normal targets afterward.
