# HelloWorld (Aiken / Invariant0 CTF)

This is the `00_hello_world` challenge from
[Invariant0's Cardano CTF](https://github.com/Invariant-0/cardano-ctf/tree/43de1e4186674f10563f30b29cc2bc1f743cf30d/00_hello_world).
The source is `validators/hello_world.ak`, validator `hello_world.hello_world`.
It accepts datum `Constr 0 []` and redeemer `Constr 0 [B "Hello CTF!"]`.
The redeemer is a record containing the bytestring, rather than a bare bytestring.

## Reproducing `hello_world.flat`

Prerequisites: Git, Python 3, and **Aiken v1.0.26-alpha+075668b** from the
[Aiken release](https://github.com/aiken-lang/aiken/releases/tag/v1.0.26-alpha).
The pinned project uses `aiken-lang/stdlib` **1.6.0**. Modern Aiken releases cannot
compile this project's original syntax. Compiler versions matter: the upstream
committed blueprint contains different bytes; rebuild it using the version below.

Starting at this repository's root, with the specified `aiken` on `PATH`:

```sh
export BLASTER_ROOT="$PWD"
HELLO_BUILD_DIR="$(mktemp -d)"
git clone https://github.com/Invariant-0/cardano-ctf.git "$HELLO_BUILD_DIR/cardano-ctf"
cd "$HELLO_BUILD_DIR/cardano-ctf"
git checkout 43de1e4186674f10563f30b29cc2bc1f743cf30d
cd 00_hello_world
aiken --version
aiken build --trace-level silent

# Extract exactly one CBOR wrapper, already supplied by compiledCode.
python3 - <<'PY'
import json, os
from pathlib import Path
blueprint = json.loads(Path("plutus.json").read_text())
code = next(v["compiledCode"] for v in blueprint["validators"]
            if v["title"] == "hello_world.hello_world")
destination = Path(os.environ["BLASTER_ROOT"]) / "Tests/Scripts/HelloWorld/hello_world.flat"
assert code == destination.read_text(), "Generated script differs from the committed artifact"
destination.write_text(code, encoding="ascii")
PY
```

The comparison above was checked byte for byte. The `.flat` extension here denotes
hex-encoded, single-CBOR-wrapped Flat UPLC, not raw Flat bytes. Do not add another
CBOR wrapper or a trailing newline. The import uses Plutus V2 and `single_cbor_hex`.

From this repository's root:

```sh
shasum -a 256 Tests/Scripts/HelloWorld/hello_world.flat
# 2cd3aba9d0c02126ad2ca71255078639b39628f08f98586db1cd484ae2181bee
```

## Checking the proofs

With this repository's Lean dependencies and the Z3 version required by Blaster:

```sh
lake build Tests.Scripts.HelloWorld.Properties
```

`Properties.lean` proves the acceptance condition in both directions and checks
that an accepted input exists. These proofs concern the imported compiled bytes.
