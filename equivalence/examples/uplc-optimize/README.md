# UPLC optimizer regressions

Start with the [step-by-step optimizer regression tutorial](tutorial/README.md). It
compares an original V3 spending validator with actual historical and corrected
optimizer outputs, and also covers the smallest integer-function reproducer.

The historical optimized fixtures listed below are actual `uplc optimize` outputs
from **1.71.0.0**, revision `261766ad1d582bce8c86bad1af7a3b0e5355b21c` (default options).

| Program | Counterexample input | Original | Optimized |
|---|---:|---|---:|
| `ifthenelse` | 0 | division by zero | 1 |
| `if-false-negative` | -3 | division by zero | 11 |
| `choose-list-empty` | 0 | division by zero | 7 |
| `choose-list-cons` | 0 | division by zero | 7 |
| `choose-data-integer` | 42 | division by zero | 9 |
| `head-list-empty` | 0 | head of empty list | 7 |
| `index-out-of-bounds` | 0 | byte index outside bounds | 7 |
| `un-i-data-bytes` | 42 | integer extraction from bytes Data | 7 |
| `invalid-utf8` | 0 | invalid UTF-8 decoding | 7 |
| `explicit-error` | 0 | explicit error | 7 |

The selected value does not exempt other builtin arguments from eager evaluation.
New counterexamples were also confirmed with `uplc evaluate` under variants E and G.
`delayed-control`, `unused-let`, and `case-field` are correctly optimized controls.

`invalid-utf8-symbolic` is another confirmed mismatch, but the CLI currently
reports unsupported `BitVec` translation when the decoder input is symbolic.
It is covered separately as a known limitation, not a successful detection.

The historical bug is fixed by [Plutus PR #8022](https://github.com/IntersectMBO/plutus/pull/8022).
`ifthenelse-fixed.uplc` and `tutorial/validator-fixed.uplc` were generated with
version **1.72.0.0**, revision `1ef5a0eef37772e35b1e587f7a3b0afa61be4358`.
The tests check both corrected outputs against their originals; the validator
comparison includes an accepted transaction witness.

Regenerate historical outputs with
`sh equivalence/examples/uplc-optimize/regenerate.sh /path/to/historical/uplc`.
Regenerate the two corrected tutorial outputs with
`sh equivalence/examples/uplc-optimize/regenerate-fixed.sh /path/to/fixed/uplc`.
Both scripts check the generator revision to protect the historical fixtures.
The Lean tests use checked-in outputs; they do not require either optimizer.
