# Scaling

`lib` is a Library as described in `prover/sig/library.md`. Terms, symbols, and Steps are described in `prover/sig/proof.md`. Evidence lists retain their argument order. An operation returning `(cons value lib)` can add auxiliary lemmas. Use the returned Library for the next operation. Every call in the table except `power-measure` can return a failure as its entire result.

| Call | Result |
|---|---|
| `(b2-scaling-rational-op lib name term evidence)` | Step proving `term` rational using the `rationalp-` fact with the operation name string `name` and the list of evidence Steps. |
| `(b2-scaling-number-of-rational lib term rational)` | Step proving `term` numeric from the Step `rational`. |
| `(b2-scaling-opposite-sign lib term rational)` | Step relating positivity of the negation of `term` to negativity of `term`, given the Step `rational`. |
| `(b2-scaling-positive-is-nonnegative lib term pos rational)` | Step proving `term` nonnegative given Steps `pos` for positivity and `rational` for rationality. |
| `(b2-scaling-scaled-sign lib value scale rat-value rat-scale positive-scale)` | Pair of the Step equating the negative sign tests on `value` and its product with `scale`, and the Library. The last three arguments are the rationality Steps for the operands and the positivity Step for `scale`. |
| `(b2-scaling-rational-scale-order lib a b scale rationals positive-scale)` | Pair of the Step equating the scaled and unscaled comparisons of `a` and `b`, and the Library. `rationals` lists the rationality Steps of `a`, `b`, and `scale`. `positive-scale` proves `scale` positive. |
| `(b2-scaling-fraction-data lib value rational)` | Pair of `(den num den-type num-type den-positive representation)` and the Library, given term `value` and its rationality Step. The first two fields are the denominator and numerator terms, followed by their integer Steps, a positive denominator Step, and the commuted representation Step. |
| `(b2-scaling-rank-gap lib value rational regime large)` | Pair of `(gap positive)` and the Library. `value` is a term, `rational` and `regime` are Steps, and `large` is the Boolean selecting the upper range. `gap` is its rank term and `positive` is a Step proving it positive. |
| `(b2-scaling-doubled lib term typed)` | Step equating twice `term` with its sum with itself, using the integer Step `typed`. |
| `(b2-scaling-expanded-fraction lib value rational denominator representation d-type n-type d-positive)` | Pair of `(scale scale-type scale-positive den-equation num-equation)` and the Library, for `value` with rationality Step `rational`. `denominator` is the proposed denominator term, `representation` its product representation Step, `d-type` and `n-type` the integer Steps, and `d-positive` the positive denominator Step. |
| `(b2-scaling-fraction-for-scaled lib x rationals large)` | Pair of `(den num den-type num-type den-positive representation)` and the Library for the scaled fraction of term `x`. `rationals` is the ordered list of the original and scaled rationality Steps. `large` selects halving when true and doubling when false. |
| `(b2-scaling-power-measure term)` | The measure term for `term` in the power-of-two helper. |
| `(b2-scaling-power-decrease lib goal evidence)` | Pair of the Step proving the power-of-two helper's decrease literal `goal` under the ordered list of evidence Steps, and the Library. |

`*b2-scaling-two*` and `*b2-scaling-half*` are quoted two and one half. `*b2-scaling-power*` is the `POWER-OF-2-HELPER` symbol.
