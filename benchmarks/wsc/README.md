# WSC containment tractability benchmark

This opt-in benchmark gives Blaster optimization branches the same WSC
containment goal to attempt. It is copied from the WSC reference implementation,
with the statement structure, helper definitions, and script bytes preserved.
The CEK fuel is **300,000 steps**, raised from the reference’s original 10,000.
It does not impose an input-size bound or supply a custom invariant.
The repository's ordinary library and test targets do not run this benchmark.

The goal is: for an accepted, valid V3 script context, an asset that is not
exempt satisfies

```text
quantity at the published base payment credential in inputs + signed mint
  ≤ quantity at that payment credential in outputs
```

The second theorem gives the bound or the asset's exemption. The complete
quantifiers and premises are visible in both proof files:

- `WscContainment/Script.lean`: import the pinned original UPLC script.
- `WscContainment/Specification.lean`: quantities, parameter decoding, exemptions.
- `WscContainment/Plain.lean`: both theorems using ordinary `blaster`.
- `WscContainment/Auto.lean`: the original `(induction: auto)` proof invocation.
- `fixtures/wsc-poc/README.md`: script provenance and SHA-256.

## Run an optimization branch

On Linux, install the repository's Lean toolchain, Z3 (the reference uses
4.15.2), GNU `time`, and GNU `timeout`. From the repository root:

```sh
cd benchmarks/wsc
./check.sh plain -KblasterRev=beta-lambda-cache-optimization

# Test a different upstream branch or a commit:
./check.sh plain -KblasterRev=YOUR_OPTIMIZATION_BRANCH_OR_COMMIT

# Test a branch in another fork:
./check.sh plain -KblasterUrl=https://github.com/OWNER/Lean-blaster \
  -KblasterRev=YOUR_BRANCH_OR_COMMIT

# Reuse an existing local checkout and its compiled artifacts:
./check.sh plain -KblasterPath=/absolute/path/to/Lean-blaster
```

The package pins the original compatible upstream library model: ledger
`5dab3c4` and PlutusCore `d85df05` (from `value-builtins`, needed for CIP-153).
Keeping these fixed isolates solver-branch comparisons and preserves the
original statement's ledger model. Current ledger `main` expects a bytestring
ordering instance absent from that older PlutusCore branch, so mixing those
defaults would fail before the proof attempt.

Override the libraries with `-KledgerRev=REF`, `-KplutusUrl=URL`, and
`-KplutusRev=REF` if needed; use a compatible pair and hold them fixed when
comparing solver branches. Every run refreshes selected git refs and saves the
resolved manifest. `-KblasterPath` takes precedence over solver URL/ref settings;
the local checkout's commit and tracked diff summary are recorded too.

The default wall-clock budget is **30 minutes**, including dependency setup.
`WSC_TIMEOUT_SECONDS=600 ./check.sh plain ...` changes it. Each SMT query uses
the original 15-second solver timeout. The runner applies an **8 GiB** memory
scope where a user systemd manager is available; elsewhere, run inside an
equivalent container limit to make resource comparisons meaningful.

Results are written to `.lake/tractability.MODE.XXXXXX/`: dependency revisions,
tool versions, logs, per-stage elapsed time and maximum RSS, and a result file.
Compare `proof.time` separately from dependency/build time and use equally warm
caches. A pass requires every selected theorem to compile and its printed
axiom list to contain no `sorryAx`. A timeout or unsuccessful proof remains a failure;
there is no expected-`Undetermined` escape hatch. Blaster's existing
`blasterProven` SMT trust mechanism is retained.

For preparation without an expensive proof attempt:

```sh
lake -R -KblasterRev=YOUR_BRANCH_OR_COMMIT update
lake -KblasterRev=YOUR_BRANCH_OR_COMMIT build WscContainment
```

## Automatic-induction reference

`./check.sh auto ...` selects the original tactic. This requires a solver that
supports `(induction: auto)`, proposed in
[Lean-blaster #285](https://github.com/input-output-hk/Lean-blaster/pull/285).
An unsupported tactic option is a compatibility failure, not a timing result;
use `plain` on ordinary upstream optimization branches. Compare branches using
the same proof mode.

The successful reference implementation and checked export are recorded at
[wsc-blaster commit 0984f4e](https://github.com/SeungheonOh/wsc-blaster/blob/0984f4eab44ce565d5c6dd7f4c744e01394bd78e/examples/README.md).
It uses that project's supporting solver and library implementations. An
upstream branch is not assumed to reproduce that result; discovering whether
it can is the purpose of this benchmark.

## Earlier DX unshaped P1 workload

`WscDx/Unshaped.lean` preserves the earlier `CardanoLedgerApiBlaster-dx`
`WSC/Benchmark/P1Unshaped.lean` workload: fully symbolic `ppCS` and rewarding
`ScriptContext`, the corrected `P1UnshapedFormH` statement, signed mint, and
`#prep_uplc` at **300,000** CEK steps followed by ordinary
`blaster (timeout: 1800)`. The input uses `toTerm ppCS :: rewardingInputs ctx` directly; every
transaction field remains symbolic.

This case uses the older production validator from wsc-poc `2306678`, rather
than the `2e815a1` validator in `WscContainment`. These are separate workloads,
not interchangeable timing results. The full historical preparation did not
reach the proof tactic. The theorem remains a real opt-in proof obligation;
this benchmark does not assert that it is tractable or already proved.

The minimal definitions come from the cleaned `CardanoLedgerApiBlaster` WSC
source: `WSC/Spec.lean`, `WSC/Model/{Ground,TransferHelpers,Registry}.lean`, and
`WSC/Props/P1Statement.lean`. Only the namespace changes. The corrected form
includes the Ada exclusion and two-field directory-node interval decoding.
Fixture provenance and the exact byte hash are in `fixtures/wsc-dx/README.md`.

```sh
./check.sh dx -KblasterRev=YOUR_OPTIMIZATION_BRANCH_OR_COMMIT
```

DX defaults to **120 seconds total** (setup, build, and proof) and a **4 GiB
hard memory limit**, including solver children. The runner requires a user
systemd manager for this mode and refuses to run without a hard memory scope.
Lean also receives `-M3000`. A larger intentional wall budget can be selected
with `WSC_TIMEOUT_SECONDS`; timeout termination allows five seconds before
force-killing the process group. No Fin or other solver compatibility patch is
applied in any mode.

On a host without a user systemd manager, run in a container with a hard
4 GiB memory limit and set `WSC_SCOPED=1` inside that container. This variable
asserts that the caller has already applied the limit; do not set it on an
unbounded host. Build caches should be equally warm when comparing proof time.
The `WscDx` library target decodes the script and checks the specification
without running `#prep_uplc`; `check.sh dx` builds it under the same caps before
attempting the complete preparation and proof.

## Recorded validation

With Lean 4.24.0 and Z3 4.15.2:

- Upstream Blaster `bafdd4f`, ledger `5dab3c4`, and PlutusCore `d85df05` build
  the fixture and specification successfully (349 jobs).
- The earlier **10,000-step** upstream `plain` attempt fails at unsupported
  `Fin` translation after 96.82 seconds of proof-stage wall time, with maximum RSS 4,471,696 KiB. This
  is a translation failure, not a timeout or a proof of the theorem.
- Both **300,000-step** `auto` theorems compile with the same WSC reference
  runtime used for the earlier 10,000-step control. Full Lean checking took
  **419.27 seconds** (about seven minutes), with maximum RSS **6,140,964 KiB**
  (about 5.9 GiB), under a hard 30 GiB memory cap and 45-minute deadline.
  Their axiom lists contain `propext`, `Classical.choice`, `Quot.sound`, and
  `Blaster.Tactic.blasterProven`, with no `sorryAx`; see
  [`validation/auto-300000.log`](validation/auto-300000.log). The committed
  `Auto.lean` matches the successfully checked source byte for byte; `plain`
  uses the same statements. The previous 10,000-step case proof reached its
  checked case at 447 seconds.
- Local-checkout selection and a 10-second deadline were exercised: setup and
  build completed, and the proof attempt correctly exited 124 as `TIMEOUT`.
- The DX fixture and specification build on the same unmodified upstream
  solver (349 jobs). The complete 300,000-step attempt times out during
  `#prep_uplc`, before `blaster`, under the 120-second total budget. Its log
  prints the preparation-start marker and never the completion marker. The
  scope's hard cap was verified as 4,294,967,296 bytes, and no Lean or solver
  children remain after timeout. This is an incomplete preparation attempt,
  not a theorem verdict.
- DX refuses to run when neither a user systemd manager nor an asserted
  external hard memory scope is available (exit 2).

## Inherited specification details

The ledger-validity premise uses this library's `validScriptContext` model.
Negative reference indices clamp to zero through `Int.toNat`. The conservative
directory exemption checks all reference inputs, including ones not selected
by the redeemer. These details are preserved from the original statement;
successful execution alone is not an unconditional containment claim.
