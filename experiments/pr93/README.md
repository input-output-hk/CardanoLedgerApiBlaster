# PlutusCoreBlaster PR #93 in CardanoLedgerApiBlaster

This branch pins PlutusCoreBlaster to PR #93 commit `07584be44ba1d4fe70c95a8e219d7e2a6d2245d9`
and its Lean-blaster dependency to `fe7a8fbe001594d8275ebb1783af8dea305f2bdd`.
The generic CEK rules are opt-in. `bench.py` prepares each tracked complete script
twice with the same dependency revisions and existing fuel: once with its
current imports, then with `PlutusCore.UPLC.Optimize.Extension` imported before
`#prep_uplc`. It measures the generated proposition's expression nodes and
whether a CEK evaluator or a traversal/search summary remains.

## Observations

Single warm runs on macOS with Lean 4.24.0, Z3 5.4.1 and one Lean worker:

| Script | Baseline | With PR #93 rules | Residual result |
| --- | ---: | ---: | --- |
| SellNFT (fuel 1,800) | 38.3 s | >120 s | Baseline: 11,588 nodes, no CEK evaluator; optimized run timed out |
| HelloWorld (10,000) | 2.13 s | 2.16 s | 103 nodes in both |
| UnlockPIN (10,000) | 2.21 s | 2.13 s | 100 nodes in both |
| ParamFeed (10,000) | 2.20 s | 2.15 s | 95 nodes in both |
| MintingPolicy (1,200) | 8.71 s | 30.25 s | 2,385 nodes in both; no search/traversal summary |
| Governance (9,000) | >60 s | >60 s | Neither run completed within the deadline |

The opt-in extension does **not** speed up these existing examples. In particular,
the SellNFT comparison shows a substantial preparation regression at the current
fuel. The completed small and minting cases retain the same residual node count
and no search/traversal summary. The timeouts do not establish the eventual
residual size or outcome. These are development timings, not stable performance
benchmarks; the unchanged residuals and timeout comparison are the main evidence.

The PR #93 rules recognize specific compiled CEK loop shapes. These examples do
not demonstrate that recognition, so this branch does not add the extension
import to the normal test modules. Its benchmark is an explicit integration
probe and can be rerun after the recognizers or compiler inputs change.

The existing `Tests.Scripts.SellNFT.SellNFT` and
`Tests.Scripts.SellNFT.Properties` Lake targets both build with these pinned
dependencies. The two intended theorems validate, and all three expected
counterexamples are still found.

## Reproduce

```sh
lake update
lake build CardanoLedgerApi PlutusCore.UPLC.Optimize.Extension
lake build Tests.Scripts.SellNFT.Properties
python3 experiments/pr93/bench.py --cases sellnft --timeout 120
python3 experiments/pr93/bench.py \
  --cases hello unlockpin paramfeed minting governance --timeout 60
```

`bench.py` writes source variants, logs and JSON results under its ignored
`.work/` directory. The time includes Lake startup, imports and elaboration;
the same script bytes, input conversion function and CEK fuel are used in each
pair.
