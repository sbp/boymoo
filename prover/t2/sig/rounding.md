# Rounding

`lib` is the library used by the T2 arithmetic tactics. Terms and Steps use
the shared proof representation. Lists of Steps are in the supplied order.
Every entry below can return a failure object in place of its result.

| Call | Result |
|---|---|
| `(t2-rounding-shifted lib proof amount)` | Step translating the comparison in `proof` by the term `amount`. |
| `(t2-rounding-quotient-upper lib)` | Library with the strict upper bound on the quotient. |
| `(t2-rounding-parts-times lib ratio)` | Step equating the product of the denominator and the rational certified by `ratio` with its numerator. |
| `(t2-rounding-numerator-sign lib ratio pos-d int-d)` | Step relating the rational's sign to its numerator's sign, given its rationality and the denominator's positivity and integrality. |
| `(t2-rounding-nonnegative-bracket lib ratio nonnegative-value)` | Steps for the integer quotient, weak lower bound, and strict upper bound, in that order. The input Steps establish rationality and nonnegativity. |
| `(t2-rounding-make-strict lib weak left-rat right-rat noninteger integral)` | Strict comparison from `weak`, rationality of its endpoints in the order of its underlying strict comparison, and evidence that one endpoint is integral and the other is nonintegral. |
| `(t2-rounding-normalized-floor lib ratio not-integer)` | Step exposing the noninteger branch of the unit floor for a rational. |
| `(t2-rounding-negative-bracket lib ratio negative-value not-integer)` | Steps for integrality of the lower endpoint, the strict lower bound, and the strict upper bound, in that order. The input Steps establish rationality, negativity, and nonintegrality. |
| `(t2-rounding-noninteger-floor lib)` | Library with the noninteger floor interval lemma. |
| `(t2-rounding-weak-then-strict lib weak strict types)` | Step composing a weak comparison with a strict one. `types` is the ordered list of rationality Steps for the endpoints of the weak comparison. |
| `(t2-rounding-integer-comparisons lib)` | Library with the two comparison lemmas for an integer and a noninteger rational. |
| `(t2-rounding-build lib)` | Library with the rounding lemmas in recipe order. |

The results of `t2-rounding-numerator-sign`,
`t2-rounding-nonnegative-bracket`, `t2-rounding-negative-bracket` and
`t2-rounding-weak-then-strict` are `(cons value lib)`, with the Step or
Step list in the table as `value`. The library carries any auxiliary
lemmas added during the call. A failure is the entire result.
