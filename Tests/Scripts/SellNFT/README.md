# SellNFT (Aiken / Invariant0 CTF)

This is the `01_sell_nft` challenge from
[Invariant0's Cardano CTF](https://github.com/Invariant-0/cardano-ctf/tree/43de1e4186674f10563f30b29cc2bc1f743cf30d/01_sell_nft).
The source is `validators/nft_sell.ak`, validator **`nft_sell.buy`**. The other
validators in that project's blueprint are not this example's script.

The datum contains the seller's address and price; the redeemer is void. The
validator requires a spending purpose and some output paying the seller at least
the price. `Properties.lean` also demonstrates a multi-satisfaction weakness.

## Reproducing `sell_nft.flat`

Prerequisites: Git, Python 3, and **Aiken v1.0.18-alpha** from the
[Aiken release](https://github.com/aiken-lang/aiken/releases/tag/v1.0.18-alpha).
The project pins `aiken-lang/stdlib` **1.6.0**. Use this compiler version for exact
reproduction: v1.0.26-alpha builds the source but produces different bytes.

Starting at this repository's root, with the specified `aiken` on `PATH`:

```sh
export BLASTER_ROOT="$PWD"
SELL_BUILD_DIR="$(mktemp -d)"
git clone https://github.com/Invariant-0/cardano-ctf.git "$SELL_BUILD_DIR/cardano-ctf"
cd "$SELL_BUILD_DIR/cardano-ctf"
git checkout 43de1e4186674f10563f30b29cc2bc1f743cf30d
cd 01_sell_nft
aiken --version
aiken build

# Default build strips traces; do not pass --keep-traces.
python3 - <<'PY'
import json, os
from pathlib import Path
blueprint = json.loads(Path("plutus.json").read_text())
code = next(v["compiledCode"] for v in blueprint["validators"]
            if v["title"] == "nft_sell.buy")
destination = Path(os.environ["BLASTER_ROOT"]) / "Tests/Scripts/SellNFT/sell_nft.flat"
assert code == destination.read_text(), "Generated script differs from the committed artifact"
destination.write_text(code, encoding="ascii")
PY
```

This reproduces the committed file byte for byte, which also matches the
`nft_sell.buy` artifact in the pinned upstream blueprint. The file contains
hex-encoded Flat UPLC wrapped once in CBOR, with no trailing newline. Import it
as Plutus V2 with `single_cbor_hex`; do not wrap `compiledCode` again.

From this repository's root:

```sh
shasum -a 256 Tests/Scripts/SellNFT/sell_nft.flat
# 15054aadd31f1ef22cf00b3ef6f5d357847c6d13d599e432171755efd5e3543a
lake build Tests.Scripts.SellNFT.Properties
```

The proof command requires the project's Lean dependencies and the Z3 version
required by Blaster. It checks the imported bytes, including the expected
counterexample to multi-satisfaction safety.
