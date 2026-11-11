# Earlier DX WSC UPLC fixture

`programmableLogicGlobal-2306678.flat` is the raw `cborHex` field from:

<https://github.com/input-output-hk/wsc-poc/blob/2306678fb03b615d4e58ae207e3eccf9b3676b9b/generated/scripts/unapplied/prod/programmableLogicGlobal.json>

- Upstream revision: `2306678fb03b615d4e58ae207e3eccf9b3676b9b`
- Raw fixture SHA-256: `eed62d595f56c3c69779c363950bc9ae81f57e9fde062b09cff8f40eb4bf5dbf`
- Raw fixture size: 5,624 bytes, with no trailing newline
- Script type: `PlutusScriptV3`
- Encoding: `double_cbor_hex`

These are the bytes used by the earlier DX `P1Unshaped.lean` benchmark via
`WSC/GlobalImport.lean` and `WSC/flats/programmableLogicGlobal.flat`. They differ
from the later `2e815a1` fixture used by `WscContainment`. The historical
300,000-step preparation budget is preserved in `WscDx/Unshaped.lean`.
