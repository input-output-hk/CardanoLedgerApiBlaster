# UPLC optimizer regressions

Original programs and actual `uplc optimize` outputs from **1.71.0.0**,
revision `261766ad1d582bce8c86bad1af7a3b0e5355b21c` (default options).

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

Regenerate with `sh equivalence/examples/uplc-optimize/regenerate.sh /path/to/uplc`.
The Lean tests use the checked-in outputs; they do not require the optimizer.
