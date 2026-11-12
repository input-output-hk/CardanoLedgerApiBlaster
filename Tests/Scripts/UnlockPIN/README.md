# UnlockPIN (Pebble)

This locally authored example is implemented in `unlock_pin.pebble`, using
[Pebble](https://github.com/HarmonicLabs/pebble). It replaces the previous
source-less script with reproducible compiler output.

The validator accepts exactly datum `Constr 0 []` and redeemer
`Constr 0 [I 6781988]`. Both complete Data values are compared, so a different
constructor, extra fields, wrong field type, or wrong PIN fails. A missing datum
also fails.

## Script interface

The Pebble implementation keeps the original **Plutus V2 / UPLC 1.0.0** interface:
three arguments, datum, redeemer, and script context. The context argument is
ignored. The Lean import and `Properties.lean` are unchanged from the original
example, including its `validSpendingContext` predicate and all three Blaster
checks.

The source exports a validator function: success returns unit, while a failed
assertion raises a UPLC error.

## Reproducing `unlock_pin.flat`

Prerequisites: Node.js 22 or newer, npm, and Python 3. The compiler and CLI are
both pinned to **0.1.1**, with transitive dependencies fixed by
`package-lock.json`. Version 0.1.1 is deliberately pinned because its compiler
honors the disabled UPLC optimizations in `pebble.config.json`. Those settings
avoid `case`/`constr` application grouping, preserving the original UPLC 1.0.0
interface. Later versions tested here emitted UPLC 1.1.0 constructs despite the
requested 1.0.0 target. npm marks 0.1.1 as deprecated in favor of 0.1.2; use the
lockfile for this example's reproducible build.

Starting at the repository root:

```sh
cd Tests/Scripts/UnlockPIN
npm ci
npm run build
git diff --exit-code -- unlock_pin.flat
```

The build runs `pebble export --function-name unlockPIN` using
`pebble.config.json`. Pebble writes raw Flat bytes to `out/out.flat`.
`encode.py` verifies the UPLC version, wraps those bytes once in a CBOR
bytestring, and writes lowercase hex without a trailing newline to
`unlock_pin.flat`. It does not modify the compiled term.

From the repository root, check the ASCII hex file's digest:

```sh
shasum -a 256 Tests/Scripts/UnlockPIN/unlock_pin.flat
# b0718d8903815ea790a8b894e54d548e6bed8339f6d16d90fe74b6f7174289bd
```

`node_modules/` and `out/` are build products and are ignored by Git.

## Checking the proofs

With the project's Lean dependencies and the Z3 version required by Blaster:

```sh
lake build Tests.Scripts.UnlockPIN.Properties
```

The theorem uses Blaster directly to prove, for every V2 spending input satisfying
`validSpendingContext`, that execution succeeds iff the PIN redeemer and void
datum match exactly. The original two `#blaster (solve-result: 1)` checks ask
Blaster to find counterexamples to the claims that arbitrary integer PINs work
and that every valid context fails. All three checks retain the ledger-validity
predicate and quantify over the full context, without fixing transaction lists
or supplying witnesses. The proofs use Blaster and its SMT backend with the same
trust assumptions as the other examples.
