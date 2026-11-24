# Addition of integer exponents

`proof` is the H1 Prover and `normalizer` is the Algebra. Their forms are
in `tactics.md` and `book-arithmetic.md`. A term and a Step have the forms
in `prover/sig/proof.md`. `tests` is an ordered list of signed tests
`(term holds)` with `t` or `nil` in the second field. `zero-base`,
`nonzero`, `equality` and `case` are Steps. This book defines no classes.

| Call | Result | Failure |
|---|---|---|
| `(h1-book-expt-sum-power base exponent)` | The `EXPT` application to `base` and `exponent`. | — |
| `(h1-book-expt-sum-number term)` | The `ACL2-NUMBERP` application to `term`. | — |
| `(h1-book-expt-sum-fixed-zero term)` | The equality of the `FIX` application to `term` and quoted zero. | — |
| `(h1-book-expt-sum-zip-when-integer proof)` | The Prover with the two lemmas relating `ZIP` to zero on integers. | A failure in place of the Prover. |
| `(h1-book-expt-sum-power-at-zero proof base equality)` | A Step for the zero-exponent power using `equality` to establish the exponent. | A failure in place of the Step. |
| `(h1-book-expt-sum-not-zip proof exponent nonzero normalizer)` | `(cons step normalizer)` with the Step disproving `ZIP` and the resulting Algebra. | A failure in place of the pair. |
| `(h1-book-expt-sum-power-shift proof base earlier later up normalizer)` | `(cons step normalizer)` with the power equation from exponent `earlier` to exponent `later` and the resulting Algebra. `up` is true for a successor. | A failure in place of the pair. |
| `(h1-book-expt-sum-power-shifts proof)` | The Prover with the successor and predecessor lemmas. | A failure in place of the Prover. |
| `(h1-book-expt-sum-addition-for-nonzero-base proof)` | The Prover with the signed exponent addition lemma for a nonzero base. | A failure in place of the Prover. |
| `(h1-book-expt-sum-install-power-addition proof)` | The Prover with the lemmas for the exponent addition tactic, installed in order. | A failure in place of the Prover. |
| `(h1-book-expt-sum-find-nonzero proof normalizer term)` | `(cons step normalizer)` with the Step disproving equality to zero, or `nil` in its place, and the resulting Algebra. It searches the ordinary and reversed equality in that order. | A failure in place of the pair. |
| `(h1-book-expt-sum-zero-of-sum proof normalizer left right)` | `(cons step normalizer)` with the Step deciding whether the sum vanishes and the resulting Algebra. | A failure in place of the pair. |
| `(h1-book-expt-sum-power-on-zero-base proof base exponent zero-base case normalizer)` | `(cons step normalizer)` with the evaluated power equation and the resulting Algebra. `case` decides whether the exponent is zero. | A failure in place of the pair. |
| `(h1-book-expt-sum-zero-base-product proof goal base left right tests)` | A Step proving `goal` on a zero base, with cases for whether the exponents `left` and `right` vanish. | A failure in place of the Step. |
| `(h1-book-expt-sum-power-addition proof formula)` | A Step proving the addition formula, including its guarded variants. | A failure in place of the Step, including `Unproved` when the tactic does not apply. |
