# Script examples and reproduction

The properties in each directory refer to its committed compiled UPLC artifact.
Rebuilding the source requires the specific compiler and options used for those
bytes. The per-example guides document the encoding, parameters, checksum, and
Lean proof command.

| Example | Language / source | Reproduction status |
| --- | --- | --- |
| [Auction](Auction/README.md) | Plinth, Plutus auction tutorial | Existing pinned build guide |
| [HelloWorld](HelloWorld/README.md) | Aiken, Invariant0 CTF `00_hello_world` | Rebuilt byte for byte with Aiken v1.0.26-alpha |
| [SellNFT](SellNFT/README.md) | Aiken, Invariant0 CTF `01_sell_nft` / `nft_sell.buy` | Rebuilt byte for byte with Aiken v1.0.18-alpha |
| [UnlockPIN](UnlockPIN/README.md) | Pebble, local source | Pinned compiler, lockfile, and build command |
| Governance | Likely Plinth, Plutus `cardano-constitution` | Exact source revision, implementation, and compiler build still unconfirmed |
| MintingPolicy | Source repository requires access | No public reproduction guide |
| ParamFeed | Source unidentified | No source build recipe yet |

The CTF scripts and UnlockPIN use the original Plutus V2 interface. Auction,
Governance, MintingPolicy, and ParamFeed use Plutus V3. In this tree most `.flat`
files are ASCII hex with a single CBOR wrapper; ParamFeed instead uses `flat_hex`.
Always follow the `#import_uplc` declaration rather than inferring the encoding
from the filename.

From the repository root, `lake build Tests.Scripts.<Example>.Properties` checks
one example, while `make build_tests` checks the full test library. Use the Z3
version required by the pinned Blaster dependency: a system Z3 without Blaster's
required tactics will fail before evaluating the properties.
