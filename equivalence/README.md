# UPLC equivalence checker: CLI reference

For installation and worked examples, start with the
[README](../README.md#uplc-equivalence-checker), the
[optimizer regression tutorial](examples/uplc-optimize/tutorial/README.md), or the
[cross-compiler escrow example](examples/two_party_escrow_old/README.md).

```sh
lake exe uplc_equiv OLD NEW [options]
lake exe uplc_equiv --help
```

OLD and NEW are paths to UPLC programs. The options below describe the CLI;
applications using `Equivalence.Checker.Config` should set their intended options
explicitly rather than rely on CLI defaults.

## Comparison modes

| Option | Default | Meaning |
| --- | --- | --- |
| `--mode validator\|function` | `validator` | Compare validator acceptance or function outcomes. |
| `--equivalence` | Off | Check both directions for validators and bounded functions. Strict function mode already checks equality. |
| `--bounded` | Off | Make the execution-step limit part of the comparison scope. |
| `--steps N` | `100000` | Execution-step bound with `--bounded`; otherwise an analysis guard. |
| `--budget CPU MEMORY` | None | Apply the same execution-unit limits independently to each script. Required for validators without `--bounded`; optional otherwise. |
| `--language VERSION` | `PlutusV3` | Function mode also accepts `PlutusV1` and `PlutusV2`. Validator checking currently supports V3 spending contexts only. |

**Validators:** by default, every input accepted by OLD must be accepted by NEW.
Use `--equivalence` to require identical acceptance. V3 acceptance requires a unit
result; successful return values are not otherwise compared. Budget exhaustion
counts as rejection. A positive validator verdict also requires a concrete,
natively replayed OLD-accepting input. Universal OLD rejection is reported as
vacuous; failure to establish acceptance or universal rejection is inconclusive.

**Strict functions:** compare returned constants and success/error outcomes over
the selected input domain. For non-identical programs, successful nonconstant
results such as closures, analysis exhaustion and optional budget exhaustion can
make the comparison inconclusive.

**Bounded functions:** observe a returned constant, or no constant for errors,
nonconstant results and exhausted limits. By default, NEW must preserve every
constant observed from OLD. `--equivalence` requires both directions.

Without `--bounded`, exhausting `--steps` is inconclusive. With it, exhaustion is
part of the observation: nonacceptance for validators, or no constant for
functions. A bounded verdict therefore applies to the stated execution bound.

Execution budgets use the bundled post-Conway cost model, not live network
parameters: V3 uses semantics variant E; function evaluation under V1/V2 uses D.
Omitting `--budget` selects uncosted execution. Optimizations can change costs,
so comparisons under execution budgets can differ from uncosted comparisons.

## Files and function inputs

| Option | Default | Meaning |
| --- | --- | --- |
| `--format FORMAT` | `.uplc` → `textual`, `.json` → `blueprint`, otherwise `single_cbor_hex` | Input encoding for both scripts. |
| `--format-left FORMAT` | Shared format | Override OLD's encoding. |
| `--format-right FORMAT` | Shared format | Override NEW's encoding. |
| `--validator-left ID_OR_TITLE` | Sole compiled validator | Select OLD’s blueprint entry by ID or exact title. |
| `--validator-right ID_OR_TITLE` | Sole compiled validator | Select NEW’s blueprint entry by ID or exact title. |
| `--inputs DOMAIN` | `valid-context` for validators; `integer` for functions | Select the input domain. `--input` is an alias. |

Supported formats: `textual`, `flat`, `flat_hex`, `single_cbor_hex`,
`double_cbor_hex`, `blueprint`. Explicit format options take precedence over
file extensions.

For [CIP-57](https://cips.cardano.org/cip/CIP-0057) blueprints, the usual filename
is `plutus.json`. Each file must contain a selected validator with `compiledCode`.
The CLI checks a declared script hash and requires the blueprint’s
`preamble.plutusVersion` to match the comparison’s `--language` (default V3).
Apply any template parameters before comparing deployed validators. The checker
uses the same input domain as for raw UPLC and does not derive restrictions from
blueprint schemas.

```sh
lake exe uplc_equiv old/plutus.json new/plutus.json \
  --validator-left escrow.spend --validator-right escrow.spend \
  --bounded --equivalence --max-inputs 1 --max-outputs 1
```

Function domains are `integer` (one raw UPLC integer), `data` (one unrestricted
Plutus Data argument), and `data3` (three unrestricted Plutus Data arguments).

## Validator inputs

| Option | Default | Meaning |
| --- | --- | --- |
| `--max-inputs N` | `2` | Include 0..N transaction inputs. |
| `--max-outputs N` | `2` | Include 0..N transaction outputs. |
| `--max-signers N` | `2` | Include 0..N signer keys. |
| `--max-earlier-spending-redeemers N` | `0` | Include 0..N spending redeemers before the current entry in the transaction redeemer map. |
| `--datum DATA` | Symbolic | Fix the spending datum. |
| `--redeemer DATA` | Symbolic | Fix the spending redeemer. |

These options are validator-only. Count limits change the domain being checked;
they are not just performance settings. Larger maxima can substantially increase
preprocessing and solving time. There are no minimum-count options or fixed
implementation caps on these maxima.

### Structured context profile

Validator queries range over structured V3 spending contexts satisfying the
formal ledger-validity predicate. The profile has these additional restrictions:

- A spending datum is present. Datum and redeemer are arbitrary Data unless fixed.
- Input references and the spending reference use typed transaction-id/index
  encodings. Inputs can have pubkey or script credentials without staking, and
  absent, hash or inline datums.
- Transaction outputs have arbitrary addresses and inline datums. Reference
  scripts are absent.
- Each input/output value has an ADA entry and one independent policy/token entry.
- The transaction redeemer map includes the current spending entry. By default
  it comes first. With `--max-earlier-spending-redeemers N`, the checker covers
  every prefix length from 0 through N. Each earlier entry has a symbolic
  spending reference and redeemer. The tail after the current entry stays
  symbolic and ledger validity still checks the map ordering.
- The validity range and remaining auxiliary fields are arbitrary Data. Integers
  and byte strings have no size bounds.

Ledger validity excludes invalid combinations, including a spending context
without a matching input. Thus `--max-inputs 0` cannot establish a nonempty
ledger-valid spending domain. Zero-output contexts can be model-valid, for
example when input ADA pays the fee and tokens are burned.

Reports describe the domain and configured limits. Concrete domain witnesses,
acceptance witnesses and counterexamples are checked against the profile and
ledger model. Model validity does not establish on-chain reachability.

### Datum and redeemer syntax

Use textual Plutus Data: `I`, `B`, `Constr`, `List` and `Map`. For example:

```sh
--datum 'Constr 0 [Constr 0 [], I 1000000]'
--redeemer 'I 1'
--datum 'B #deadbeef'
```

Bare integers are shorthand for `I n`.

```sh
--redeemer 1           # I 1
--redeemer -42         # I -42
```

Use `--datum 'B #68656c6c6f'` for the UTF-8 bytes of `hello`. Explicit Data can
also be parenthesized, as in `--datum '(I 42)'`.

Fixing a value restricts the claim to that value. Other context fields remain
symbolic. Reports include `fixed_datum` and/or `fixed_redeemer`; native replay and
exported Lean queries use the same restrictions.

## Search and resource limits

| Option | Default | Meaning |
| --- | --- | --- |
| `--timeout SECONDS` | `20` | Z3 deadline per query, including submission. Portfolio workers share this deadline. |
| `--wall-timeout SECONDS` | `180` | Deadline for the whole check, including preprocessing and translation. |
| `-jN`, `-j N` | `1` | Race N Z3 workers on the same query. |
| `--seed S` | `0` | Starting seed; workers use S through S+N−1. |
| `--split-dispatch` | Off | Discover datum/redeemer cases and check them separately before full-domain fallback. |
| `--dispatch-cases N` | `16` | Maximum discovered cases, plus a catch-all; enables dispatch splitting. |
| `--dispatch-timeout SECONDS` | `10` | Deadline per dispatch-case query, including preprocessing; enables dispatch splitting. |
| `--skip-old-rejected` | Off | Skip the deferred universal OLD-rejection query. After preservation is proved, the checker can still search for the OLD-acceptance witness required for a positive verdict. |

### Solver workers

`--seed 42 -j4` uses seeds 42, 43, 44 and 45. Seeds, including the final worker's
seed, must fit in an unsigned 32-bit integer. The first conclusive result wins.
An early `unknown` leaves the other workers running. Workers can retrieve models
in parallel, and a `sat` result is eligible after its model arrives.
Counterexamples still need native replay. The other workers stop when a result
wins or their shared deadline is reached.

Preprocessing and SMT translation run once. Extra workers use more CPU and memory
and can help Z3 search, but do not accelerate preprocessing.

### Dispatch splitting

Discovery recognizes equality-based dispatch on constructor tags, integers, byte
strings, UTF-8 text and literal Data, including nested constructor/list/map
patterns. Undetermined fields remain symbolic, and fixed datum/redeemer options
are respected.

A found difference must replay on the original programs. A proof must cover all
parts of a disjoint partition, including a catch-all for undiscovered values and
malformed shapes. Discovery limits, timeouts or unsupported cases cannot silently
remove inputs from the claim. Incomplete proofs fall back to full-domain queries;
completed directional proofs can be retained. Use `--equivalence` when both
directions are required. Dispatch outcomes are included in the JSON `dispatch`
object.

## Reports and exports

| Option | Default | Meaning |
| --- | --- | --- |
| `--json` | Off | Print the final report as JSON instead of readable text. |
| `--emit-assurance DIR` | None | Export assurance evidence for a NEW blueprint to a fresh directory. |
| `--emit-lean FILE` | None | Export the checked Lean queries with the same domain and bounds. |
| `-h`, `--help` | — | Print usage and options. Running without arguments also prints help. |

Prefix a dash-prefixed export name with `./`, as in `--emit-lean ./--json`.

Progress is printed on stderr with elapsed time and the current phase. The final
report is printed on stdout. Text counterexamples show both outcomes and a named
V3 context, including exact lovelace and decimal ADA amounts. Application-specific
payloads retain textual Data syntax.

JSON includes the verdict, query outcomes, domain and limits, and applicable
counterexample or acceptance-witness information. Timeouts identify their phase;
`query_diagnostics` can retain an auxiliary query's timeout even when another
query or native witness later establishes the final verdict. Read the final
verdict rather than treating each diagnostic as the overall outcome.

Exported Lean files require the matching project dependencies. Each exported
query uses one solver. Active queries record their conclusive results and use
the winning seed for portfolio runs. Inconclusive queries appear as comments
that can be uncommented to retry them. The initial export and the original
full-domain queries in dispatch exports also appear as comments. Native witness
validation remains separate. CLI verification uses Blaster's SMT result without
reconstructed Lean proof terms.

### Export assurance evidence

When NEW is a blueprint, `--emit-assurance DIR` saves a completed comparison:

```sh
lake exe uplc_equiv old/plutus.json new/plutus.json \
  --validator-left escrow.spend --validator-right escrow.spend \
  --bounded --equivalence --max-inputs 1 --max-outputs 1 \
  --emit-assurance escrow-evidence
```

Choose a new directory under an existing parent. The export contains:

- `assurance.json` references the NEW blueprint by local path and SHA-256, names
  the selected validator, and records the comparison claim and evidence outcome.
- `comparison.json` records both inputs and their file digests, the selected
  script hashes for blueprint inputs, the effective settings, and the full
  checker report including any replayed counterexample. Its SHA-256 is recorded
  in the assurance document.

The export uses the draft assurance schema bundled with PlutusCoreBlaster.
`#verify_blueprint` can check the blueprint and artifact bindings. The comparison
is historical evidence with a natural-language statement, so that command does
not rerun it. To repeat the comparison, run `uplc_equiv` with the recorded inputs
and settings. The generated blueprint reference is an absolute local path.

A replayed difference is recorded as `falsified`, a positive verdict as
`verified`, a vacuous verdict as `partial`, and an inconclusive verdict as
`inconclusive`. Export starts after the checker returns a verdict. A tool error or timeout that
interrupts the comparison produces no assurance evidence. The regular report and exit status retain their
usual meanings.

### Verdicts and exit codes

| Verdict | Exit code | Meaning |
| --- | ---: | --- |
| `preserved`, `bounded_preserved` | 0 | OLD acceptance or observed function constants are preserved by NEW. |
| `equivalent`, `bounded_equivalent` | 0 | The requested equality holds in the declared domain and limits. |
| `regression`, `bounded_regression` | 1 | A replayed counterexample violates OLD → NEW preservation. |
| `inequivalent`, `bounded_inequivalent` | 1 | A replayed counterexample distinguishes the scripts. |
| `inconclusive` | 2 | A timeout, unknown result, exhausted analysis or missing validated evidence prevents a conclusion. |
| `error` | 3 | Invalid arguments, unsupported input or a tool failure. |
| `vacuously_preserved`, `vacuously_equivalent`, `vacuously_bounded_preserved`, `vacuously_bounded_equivalent` | 4 | Validator OLD rejects every input in the domain. |

On Linux and macOS, Ctrl-C and SIGTERM stop the checker and its solver workers. The CLI exits
with status 130 for Ctrl-C and 143 for SIGTERM.

Positive validator verdicts require an OLD-accepting witness in addition to valid
preservation queries. A `valid` query by itself need not establish the final
verdict. A timeout is never evidence of equivalence.
