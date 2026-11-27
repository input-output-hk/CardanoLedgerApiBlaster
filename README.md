# CardanoLedgerApi - Formal Cardano Ledger API for Lean4

[![Lean Version](https://img.shields.io/badge/Lean-v4.24.0-blue.svg)](https://github.com/leanprover/lean4)
[![License](https://img.shields.io/badge/license-Apache%202.0-blue.svg)](LICENSE)
[![Contributions Welcome](https://img.shields.io/badge/contributions-welcome-brightgreen.svg)](CONTRIBUTING.md)

CardanoLedgerApi provides a formal Lean4 model of the Cardano Ledger API — the script context types and ledger rules used by Plutus smart contracts (V1, V2, V3). Combined with [Blaster](https://github.com/input-output-hk/Lean-blaster), it enables automated formal verification of Cardano validators directly from their compiled UPLC bytecode.

## Table of Contents

- [Table of Contents](#table-of-contents)
- [Installation](#installation)
  - [Prerequisites](#prerequisites)
  - [Adding as a dependency](#adding-as-a-dependency)
- [How to use?](#how-to-use)
  - [Importing a UPLC validator](#importing-a-uplc-validator)
  - [Preparing the validator for verification](#preparing-the-validator-for-verification)
  - [Writing and verifying properties](#writing-and-verifying-properties)
- [Features](#features)
  - [Supported Ledger API Versions](#supported-ledger-api-versions)
  - [Ledger Rules](#ledger-rules)
  - [IsData Encoding](#isdata-encoding)
- [Examples](#examples)
  - [HelloWorld](#helloworld)
  - [UnlockPIN](#unlockpin)
  - [SellNFT](#sellnft)
  - [ParamFeed](#paramfeed)
  - [Functions: Fibonacci](#functions-fibonacci)
- [UPLC equivalence checker](#uplc-equivalence-checker)
  - [Build the checker](#build-the-checker)
  - [Cross-compiler escrow counterexample](#cross-compiler-escrow-counterexample)
  - [Compare your own programs](#compare-your-own-programs)
  - [Choose the input domain and limits](#choose-the-input-domain-and-limits)
  - [Read the result](#read-the-result)
  - [Library API](#library-api)
  - [Running the equivalence tests](#running-the-equivalence-tests)
- [General Description](#general-description)
  - [API Versions and Types](#api-versions-and-types)
  - [Ledger Rules as Decidable Predicates](#ledger-rules-as-decidable-predicates)
  - [IsData Class](#isdata-class)
- [Contributing](#contributing)
  - [Ways to Contribute](#ways-to-contribute)


## Installation

### Prerequisites

CardanoLedgerApi requires:

- **Lean4** v4.24.0 (or compatible version)
- **Blaster** (for property verification) — see [Lean-blaster](https://github.com/input-output-hk/Lean-blaster)
- **PlutusCoreBlaster** — see [PlutusCoreBlaster](https://github.com/input-output-hk/PlutusCoreBlaster)

### Adding as a dependency

Add the following to your `lakefile.lean`:

```lean4
require «CardanoLedgerApi» from git
  "https://github.com/input-output-hk/CardanoLedgerApiBlaster" @ "main"
```

Or in `lakefile.toml`:

```toml
[[require]]
name = "CardanoLedgerApi"
git = "https://github.com/input-output-hk/CardanoLedgerApiBlaster"
rev = "main"
```

## How to use?

### Importing a UPLC validator

Use the `#import_uplc` command to load a compiled Plutus script from a `.flat` file:

```lean4
import PlutusCore.UPLC
import CardanoLedgerApi.V2

#import_uplc myValidator PlutusV2 single_cbor_hex "path/to/my_validator.flat"
```

### Preparing the validator for verification

Use `#prep_uplc` to apply the validator to a set of inputs and produce a symbolic representation for formal reasoning:

```lean4
open CardanoLedgerApi.V2 (spendingInputs)

#prep_uplc appliedMyValidator myValidator spendingInputs 10000
```

The third argument is the input constructor (e.g., `spendingInputs`, `mintingInputs`) and the fourth is the evaluation fuel bound.

### Writing and verifying properties

Once the validator is prepared, write properties about its behaviour and discharge them with `blaster`:

```lean4
import Blaster
open CardanoLedgerApi.V2

-- Theorem: validator succeeds iff the redeemer has the expected shape
theorem successful_iff_expected_redeemer :
  ∀ (input : SpendingInput),
    validSpendingContext input →
    (isSuccessful (appliedMyValidator.prop input) ↔ isExpectedRedeemer input) := by blaster

-- Use #blaster to assert a property is falsified (i.e., find a counterexample)
#blaster (gen-cex: 0) (solve-result: 1) [cannot_unlock_validator]
```

The `validSpendingContext` predicate encodes the Cardano ledger rules, constraining the `ScriptContext` to only well-formed transaction contexts.

## Features

### Supported Ledger API Versions

| Version | Module | Script Purposes |
|---------|--------|-----------------|
| V1 | `CardanoLedgerApi.V1` | Spending, Minting, Rewarding, Certifying |
| V2 | `CardanoLedgerApi.V2` | Spending, Minting, Rewarding, Certifying |
| V3 | `CardanoLedgerApi.V3` | Spending, Minting, Rewarding, Certifying, Voting, Proposing |

Each version exposes the same core interface (`SpendingInput`, `MintingInput`, `ScriptContext`, `TxInfo`, etc.) with version-specific extensions (e.g., `txInfoReferenceInputs` in V2/V3, governance fields in V3).

### Ledger Rules

The library encodes the Cardano ledger rules as decidable boolean predicates. These constrain the `ScriptContext` seen by a validator to only contexts that the ledger would actually produce:

- `validSpendingContext` — ledger rules for a V1 spending script context
- `validMintingContext` — ledger rules for a minting script context
- `validRewardingContext` — ledger rules for a rewarding script context
- `validCertifyingContext` — ledger rules for a certifying script context

Each predicate enforces:
1. Valid script purpose (e.g., spending input exists and has a datum hash in the witness map)
2. Valid transaction inputs (sorted by `TxOutRef`, positive Ada values)
3. Valid transaction outputs (script outputs have datum hashes)
4. Valid fee (non-zero Ada only)
5. Valid minted value (sorted currency symbols and token names)
6. Sorted withdrawals, signatories, and datum map
7. ADA balance (`inputs + reward withdrawals = outputs + fee`) and non-ADA asset balance including minting and burning

### IsData Encoding

The library provides an `IsData` typeclass for bidirectional conversion between Lean4 types and the Plutus `Data` type. Instances are provided for all ledger API types, and user-defined datum/redeemer structures can implement it:

```lean4
structure SellDatum where
  seller : Address
  price  : Integer

instance : IsData SellDatum where
  toData x := mkDataConstr 0 [IsData.toData x.seller, IsData.toData x.price]
  fromData
  | Data.Constr 0 [r_addr, Data.I p] =>
      match IsData.fromData r_addr with
      | some addr => some ⟨addr, p⟩
      | none => none
  | _ => none
```

## Examples

Examples are provided in the `Tests` folder.

### HelloWorld

`Tests/Scripts/HelloWorld` — a simple password-check validator. The redeemer must be the bytestring `"Hello CTF!"` and the datum must be void.

```lean4
/-- helloWorld successful ↔ expected redeemer ∧ datum is void -/
theorem successful_iff_valid_redeemer_and_void_datum :
  ∀ (input : SpendingInput),
    validSpendingContext input →
    (isSuccessful (appliedHelloWorld.prop input) ↔ isExpectedRedeemer input ∧ isVoidDatum input) := by blaster
```

The example also uses `#blaster (solve-result: 1)` to confirm that the validator is breakable (i.e., there exists a valid input that unlocks it).

### UnlockPIN

`Tests/Scripts/UnlockPIN` — a PIN-based validator where the redeemer must match a specific integer. Demonstrates the same pattern as HelloWorld but with an integer PIN instead of a bytestring password.

```lean4
/-- unlockPIN successful ↔ expected redeemer ∧ datum is void -/
theorem successful_iff_valid_pin_and_void_datum :
  ∀ (input : SpendingInput),
    validSpendingContext input →
    (isSuccessful (appliedUnlockPIN.prop input) ↔ isExpectedRedeemer input ∧ isVoidDatum input) := by blaster
```

### SellNFT

`Tests/Scripts/SellNFT` — an NFT sale validator. The datum encodes seller address and price; the script succeeds only when the seller is paid the correct amount.

```lean4
/-- sellNFT successful → spending purpose ∧ seller is paid with expected Ada -/
theorem sell_nft_successful_imp_seller_is_paid :
  ∀ (input : SpendingInput),
     validSpendingContext input →
     isSuccessful (appliedSellNFT.prop input) →
     (isSpendingPurpose input.ctx ∧ sellerIsPaid input) := by blaster

/-- seller is not paid → sell nft errors -/
theorem seller_not_paid_sell_nft_error :
  ∀ (input : SpendingInput),
     validSpendingContext input →
     ¬ sellerIsPaid input →
     isUnsuccessful (appliedSellNFT.prop input) := by blaster
```

This example also demonstrates vulnerability discovery: `#blaster (solve-result: 1)` finds a counterexample showing that SellNFT is vulnerable to a multi-satisfaction attack.

### ParamFeed

`Tests/Scripts/ParamFeed` — a parameterised oracle price feed validator (V3). The script takes three `Data` parameters; the theorem proves that successful execution implies the parameters satisfy a matching condition.

```lean4
theorem successful_imp_valid_params :
  ∀ (params1 params2 params3 : Data) (ctx : ScriptContext),
     isSuccessful (appliedParamFeed.prop params1 params2 params3 ctx) →
     isMatchingOraclePriceParams params1 params2 params3 := by blaster
```

### Functions: Fibonacci

`Tests/Functions/Fibonacci` — property verification of pure UPLC functions, independent of the ledger API. Proves the Fibonacci recurrence relation and equivalence between two implementations.

```lean4
-- ∀ (n : Integer), n > 1 → Fibonacci n = Fibonacci (n - 1) + Fibonacci (n - 2)
theorem fibonacci_sum :
  ∀ (n r1 r2 r3 : Integer), n > 1 →
    (fromFrameToInt $ compiledSeungheonOhSize.prop n) = some r1 →
    (fromFrameToInt $ compiledSeungheonOhSize.prop (n - 1)) = some r2 →
    (fromFrameToInt $ compiledSeungheonOhSize.prop (n - 2)) = some r3 →
    r1 = r2 + r3 := by blaster

-- Equivalence between two Fibonacci implementations
theorem fibonacci_equiv :
  ∀ (n : Integer),
    (fromFrameToInt $ compiledNaiveRecursion.prop n) = (fromFrameToInt $ compiledSeungheonOhSize.prop n) := by blaster
```

## UPLC equivalence checker

`uplc_equiv` compares UPLC programs from optimizers, compiler versions or different
implementations. It can prove the requested relationship within a declared input
domain and execution limits, or find a counterexample and replay both programs on
that input.

### Build the checker

On Linux or macOS, install [elan](https://github.com/leanprover/elan), Git, a C
compiler available as `cc`, and
[Z3 5.4.0](https://github.com/Z3Prover/z3/releases/tag/z3-5.4.0). Put Z3's `bin`
directory on `PATH`. Elan selects the Lean version in `lean-toolchain`; Lake fetches
the pinned library dependencies.

```sh
git clone https://github.com/input-output-hk/CardanoLedgerApiBlaster.git
cd CardanoLedgerApiBlaster
lake build uplc_equiv
```

The checked-in examples do not require their original compilers to be installed.

### Cross-compiler escrow counterexample

This command finds a context accepted by the historical Scalus escrow
implementation and rejected by the Plinth implementation:

```sh
lake exe uplc_equiv \
  equivalence/examples/two_party_escrow_old/Scalus_0.18.2_Unisay.cbor_hex \
  equivalence/examples/two_party_escrow_old/Plinth_1.67.0.0_Unisay.cbor_hex \
  --bounded --max-inputs 1 --max-outputs 1
```

Expected: **`bounded_regression`**, exit status **1**. A reference run discovers
an output of **75,000,000 lovelace (75 ADA)** without being supplied a datum,
redeemer, amount or transaction template. The reported context passes ledger-model
validation, and native replay confirms both outcomes.

The [escrow walkthrough](equivalence/examples/two_party_escrow_old/README.md)
explains the counterexample and historical scenario. For an actual optimizer bug,
follow the [optimizer regression tutorial](equivalence/examples/uplc-optimize/tutorial/README.md):
detect the faulty optimization of a V3 validator, then verify the corrected output
using the same comparison limits.

### Compare your own programs

The first script is OLD and the second is NEW. **Validator mode** is the default:
NEW must accept every input accepted by OLD. Add `--equivalence` to require the
same acceptance in both directions, as normally needed when checking an
optimization:

```sh
lake exe uplc_equiv old.cbor_hex new.cbor_hex \
  --bounded --equivalence --max-inputs 1 --max-outputs 1
```

`--bounded` compares acceptance within an execution-step limit (default 100,000;
set it with `--steps N`). Step exhaustion counts as nonacceptance in this mode.
Without `--bounded`, validator checks require `--budget CPU MEMORY`; the step
limit then acts as an analysis guard, whose exhaustion is inconclusive:

```sh
lake exe uplc_equiv old.cbor_hex new.cbor_hex \
  --equivalence --budget 10000000 100000
```

The same execution-unit limits are applied independently to each script. Budget
exhaustion counts as rejection, so changes in execution costs can affect
acceptance under a budget. Bounded, uncosted checks omit that budget comparison.

**Function mode** compares returned constants and success/error outcomes, using
one integer input and uncosted execution by default:

```sh
lake exe uplc_equiv old.uplc new.uplc --mode function
```

The CLI recognizes textual `.uplc` files and CIP-57 JSON blueprints such as
`plutus.json`. Other paths default to single-CBOR hex. If a blueprint contains
several compiled validators, use `--validator-old` or `--validator-new` to select
one by ID or title.
Strict function mode already checks equality of outcomes. Its bounded mode instead
preserves observed OLD constants unless `--equivalence` is requested.

### Choose the input domain and limits

Validator checking supports structured, ledger-model-valid spending transactions
with a present datum. For a V2-to-V3 port, use `--language-old PlutusV2 --language-new PlutusV3`.
The checker encodes each symbolic spend for both versions. See the
[mixed-language domain](equivalence/README.md#plutus-v2-and-v3-spending-comparisons)
and the [standard V3 profile](equivalence/README.md#structured-context-profile).
Use `--purpose mint` to compare [V2 and V3 minting policies](equivalence/README.md#minting-policy-comparisons).

| Setting | Default | Purpose |
| --- | --- | --- |
| `--max-inputs N` | 2 | Include up to N transaction inputs. |
| `--max-outputs N` | 2 | Include up to N transaction outputs. |
| `--max-signers N` | 2 | Include up to N signer keys. |
| `--max-earlier-spending-redeemers N` | 0 | Include up to N spending redeemers before the current map entry. |
| `--datum DATA`, `--redeemer DATA` | Symbolic | Fix a value to focus the comparison. |
| `--timeout SECONDS` | 20 | Bound each Z3 query. |
| `--wall-timeout SECONDS` | 180 | Bound the complete check, including preprocessing. |

Start with small count limits and expand them as needed. These settings change
the domain of the claim; they are not merely performance hints. Fixing datum or
redeemer similarly restricts the claim to those values. Data accepts explicit
syntax such as `--datum 'Constr 0 [Constr 0 [], I 1000000]'` or `--datum 'B #68656c6c6f'`
for bytes. Bare integers are shorthand, so `--redeemer 1` means `--redeemer 'I 1'`.

For slow solver searches, `-j4` races four Z3 workers with different seeds;
`--seed 42 -j4` uses 42 through 45. This uses more CPU and memory and does not
accelerate preprocessing. `--split-dispatch` can discover datum/redeemer cases
and check them separately, with full-domain fallback when needed.

See the [complete CLI reference](equivalence/README.md) for every option, supported
encoding, Data syntax, dispatch settings and detailed comparison semantics.

### Read the result

| Result | Exit code | Meaning |
| --- | ---: | --- |
| `preserved` / `equivalent`, including `bounded_` variants | 0 | The requested relationship holds in the stated scope. |
| `regression` / `inequivalent`, including `bounded_` variants | 1 | A natively replayed counterexample distinguishes the scripts. |
| `inconclusive` | 2 | The checker could not establish a result within its limits. |
| `error` | 3 | Invalid arguments, unsupported input or a tool failure. |
| `vacuously_…` | 4 | OLD rejects every input in the validator domain. |

A positive validator verdict requires a concrete OLD-accepting witness as well
as successful preservation queries. A timeout, an individual `valid` query or
failure to find a counterexample is not by itself an equivalence result.

Progress goes to stderr; the final report goes to stdout. Counterexamples show
both outcomes and a readable context with datum, redeemer, inputs, outputs and
ADA amounts. Add `--json` for machine-readable results or `--emit-lean FILE` to
export the queries. Verification uses Blaster's SMT results without reconstructed
Lean proof terms. Ledger-model validity does not establish on-chain reachability.

### Library API

Build the reusable library with `lake build UplcEquivalence`. Applications can call
`Equivalence.Checker.check options old new` with decoded UPLC programs and a
`Checker.Config`. It returns the report; optional `Solver.Observer` callbacks
receive progress and phase changes. Library calls are silent by default.

### Running the equivalence tests

With the build prerequisites above and Python 3.9 or later installed, run:

```sh
make check_equivalence
```

This checks the solver prerequisites, rebuilds the CLI and library, and runs the
Lean and Python integration tests, including the optimizer tutorial fixtures.
For performance measurements over the collected examples, see the
[corpus benchmarking guide](equivalence/benchmarks/CORPUS.md).


## General Description

### API Versions and Types

The library mirrors the Cardano Plutus ledger API across three versions. Each version lives under its own namespace (`CardanoLedgerApi.V1`, `CardanoLedgerApi.V2`, `CardanoLedgerApi.V3`) and re-exports the relevant types:

- **Address, Credential** — payment and staking credentials
- **Value** — multi-asset token bundles
- **TxOut, TxInInfo** — transaction outputs and inputs
- **TxInfo** — the full pending transaction view
- **ScriptPurpose, ScriptContext** — the validator's execution context
- **SpendingInput, MintingInput, ...** — typed wrappers that bundle datum/redeemer/context

V2 extends V1 with reference inputs and inline datums. V3 extends V2 with governance types (`TxCert`, `Voter`, `ProposalProcedure`, etc.) and additional script purposes.

### Ledger Rules as Decidable Predicates

A key design goal of CardanoLedgerApi is to encode the Cardano ledger rules as Lean4 decidable predicates. This is essential for formal verification: by asserting `validSpendingContext input` as a hypothesis, the SMT backend (Blaster) is constrained to only explore transaction contexts that the ledger would accept, producing meaningful and sound results.

The predicates are fully documented inline with the formal ledger specification they implement, including the exact invariants being checked (sortedness, value validity, balance, etc.).

### IsData Class

The `IsData` class, defined in `CardanoLedgerApi/IsData/Class.lean`, provides the bridge between Lean4 types and the Plutus `Data` type used on-chain. All ledger types come with `IsData` instances, and the library provides helpers (`mkDataConstr`, `toTerm`) for building instances for user-defined types.

## Contributing

We welcome all contributions! Whether it's bug reports, feature requests, documentation improvements, or code contributions, your help is appreciated.

### Ways to Contribute

- Report bugs and issues
- Suggest new features or improvements
- Add support for additional Cardano ledger rule versions
- Contribute new validator examples
- Improve documentation

**Maintained by:**
- [Jean-Frédéric Etienne](https://github.com/etiennejf)
- [Romain Soulat](https://github.com/RSoulatIOHK)
- [Mark Petruska](https://github.com/mpetruska)

**Questions?** Feel free to [open an issue](https://github.com/input-output-hk/CardanoLedgerApiBlaster/issues) or reach out to the maintainers.
