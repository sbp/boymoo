# Rational scaling

The Library, terms, and Steps have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. Each function can return a failure in place of its
listed result. A function that adds lemmas returns the updated Library,
with entries in the order in which the function adds them.

| ACL2 call | Result |
|---|---|
| `(t2-rational-scaling-negative-number lib numeric nonpositive different)` | Step proving a value less than zero. The input Steps establish that the same value is an ACL2 number, is not positive, and is distinct from zero. |
| `(t2-rational-scaling-positive-fixed lib value)` | Step equating positivity of term `value` with positivity of its numeric fix. |
| `(t2-rational-scaling-positive-integer-scale lib)` | Library with the positive integer scaling lemma. |
| `(t2-rational-scaling-positive-rational-scale lib)` | Library with the positive rational scaling and rational scale positivity lemmas, in that order. |
| `(t2-rational-scaling-mixed-order lib)` | Library with the positive, negative, and signed rational order lemmas, in that order. |
| `(t2-rational-scaling-reduce-product-comparison lib equation factor value right-slot)` | Comparison equality Step obtained from `equation` by reducing the zero product and putting `factor` second in the product with `value`. The terms are `factor` and `value`, and `right-slot` is the index of their product in the left comparison. |
| `(t2-rational-scaling-sign-inferences lib)` | Library with the eight rational scale sign lemmas. The sign of the value, the sign of the factor, and strictness are visited in that nesting order, true before false for each. |
| `(t2-rational-scaling-truth-value lib test evidence)` | Step equating comparison term `test` to its Boolean value, using the Step `evidence`. The value is true when the first literal of `evidence` equals `test`. |
| `(t2-rational-scaling-zero-scaled lib first second zero position)` | Step equating the product of terms `first` and `second` to zero using Step `zero`, which establishes that the factor at index `position` is zero. |
| `(t2-rational-scaling-negative-product-zero-branch test position conditions lib comparison expected)` | Step equating comparison term `comparison` to expression term `expected` in the zero branch. The zero test is term `test`, the zero factor has index `position`, and `conditions` is the list of Steps already in scope. |
| `(t2-rational-scaling-negative-product lib)` | Library with the rational scale negative expression lemma. |
| `(t2-rational-scaling-rational-difference-sign lib multiplier ratio sign positive-multiplier)` | Step relating the sign of the scaled difference to the sign of the original difference. The scale factor is term `multiplier`, the Step `ratio` establishes rationality of the difference, the Step `sign` establishes the strict sign of the factor, and Boolean `positive-multiplier` selects the positive sign. |
| `(t2-rational-scaling-rational-operands lib)` | Library with the rational operands signed order lemma. |
| `(t2-rational-scaling-build lib)` | Library extended by positive integer scale, positive rational scale, mixed order, sign inferences, negative product, and rational operands, in that order. |

The Step results of `reduce-product-comparison`, `truth-value`,
`zero-scaled`, `negative-product-zero-branch`, and
`rational-difference-sign` are returned as `(cons step lib)`, even
when the Library is unchanged. The returned Library carries any
`PRODUCT-ZERO` or `BOOL-TRUE` entry added by the recipe. A failure is
the entire result.
