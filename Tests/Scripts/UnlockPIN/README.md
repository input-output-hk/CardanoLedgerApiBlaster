# UnlockPIN (Pebble)

This locally authored example is implemented in `unlock_pin.pebble`, using
[Pebble](https://github.com/HarmonicLabs/pebble). It replaces the previous
source-less script with reproducible compiler output.

The validator accepts exactly datum `Constr 0 []` and redeemer
`Constr 0 [I 6781988]`. Both complete Data values are compared, so a different
constructor, extra fields, wrong field type, or wrong PIN fails. A missing datum
also fails.

## Script interface

The Pebble implementation targets **Plutus V3 / UPLC 1.1.0**, taking one encoded
`ScriptContext`. It extracts the datum from `SpendingScript` and the redeemer from
the context. This differs from the former Plutus V2 three-argument interface.
The Lean import and property context types follow that interface; the PIN and
datum acceptance conditions are unchanged.

The source exports a single validator function rather than returning a Boolean:
success returns unit, while a failed assertion raises a UPLC error.

## Reproducing `unlock_pin.flat`

Prerequisites: Node.js 22 or newer, npm, and Python 3. The compiler and CLI are
both pinned to **0.1.10**, with transitive dependencies fixed by
`package-lock.json`. This version emits UPLC constructs supported by this
repository's decoder; newer Pebble versions may target additional constructs.

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
# dc2e6cd08233e3e9e002f1bf52c5ff369b8a03ad118d4ced730caf6e26db1f16
```

`node_modules/` and `out/` are build products and are ignored by Git.

## Checking the proofs

With the project's Lean dependencies and the Z3 version required by Blaster:

```sh
lake build Tests.Scripts.UnlockPIN.Properties
```

The main theorem proves, for every valid V3 spending context, that execution
succeeds iff the PIN redeemer and void datum match exactly. A stronger theorem
establishes that equivalence without ledger-validity assumptions. Two explicit
transaction witnesses refute the original claims that arbitrary integer PINs
work and that every valid context fails; `native_decide` checks their ledger
validity. Blaster and its SMT backend carry the same trust assumptions as the
other examples, and the witness validity checks additionally trust Lean's native
evaluation.
