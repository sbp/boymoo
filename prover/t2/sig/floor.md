# Floor and divisor bounds

The constants are `*t2-floor-floor*`, `*t2-floor-equal-num*`, `*t2-floor-atom*`,
`*t2-floor-endp*`, `*t2-floor-print-base*`, `*t2-floor-member*` and
`*t2-floor-reciprocal*`. `lib` is the Arithmetic library. Terms and Steps use
the forms in `prover/sig/proof.md`. `integers` is a list of integer evidence
Steps in argument order. A result of `(cons value lib)` includes the Library's
resulting entries and facts in insertion order. All calls can return a failure.

| Call | Result |
|---|---|
| `(t2-floor-conjunction lib test consequence)` | A Step for the conjunction of the literals of the given Steps. |
| `(t2-floor-cancel-reciprocal lib factor value integers pos-factor)` | A Step cancelling the reciprocal of `factor` in its product with `value`. `pos-factor` proves the factor positive. |
| `(t2-floor-reduced-fraction lib i b integers pos-b)` | `(step int-n int-d pos-d)` for the cross product equality, numerator and denominator integrality, and denominator positivity. `i` and `b` are dividend and divisor terms and `pos-b` proves the divisor positive. |
| `(t2-floor-multiply-by-one lib factor value test integers)` | A Step reducing a product of the terms `factor` and `value` to `value` under the term `test`. |
| `(t2-floor-positive-floor-result lib floor natural-n pos-d integers)` | `(cons (list natural bound) lib)` for the floor term, given Steps proving the reduced numerator natural and the reduced denominator positive. |
| `(t2-floor-build-positive-floor lib)` | Library with the positive floor count decrease lemma. |
| `(t2-floor-constant-members n lib member formula)` | A Step for `formula` under the quoted-list membership Step `member`. Pass `1000000` as the initial fuel. |
| `(t2-floor-print-base-facts lib base premise)` | `(cons (list integral wide) lib)`. `base` is a term and `premise` is a Step for its print-base test. |
| `(t2-floor-divisor-bounds lib base hypotheses)` | `(cons (list (list integral wide) hypotheses) lib)` for divisor term `base`. |
| `(t2-floor-positive-floor-decrease lib input-value base hypotheses positive-input)` | `(cons (list step hypotheses) lib)`, proving count descent for the floor of `input-value` with divisor `base`. `positive-input` is a Step. |

`(t2-floor-divisor-bounds-query lib base hypotheses replies)` and
`(t2-floor-positive-floor-decrease-query lib input-value base hypotheses positive-input replies)`
also accept the replies of `descent-query-recipe` from `prover/sig/descent.md`.
They can return a descent request as well as a failure or the results above.
The calls without `replies` use shared Hypotheses, as do queries with `:plain`
replies.

In the ordinary entry points and with `:plain` replies, the hypothesis
argument can also be a RulerFacts context from `prover/t2/sig/guarded-selectors.md`.
The resulting hypothesis context has the same form as its input.
