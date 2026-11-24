# Signed halving

The constants are `*t2-half-two*` and `*t2-half-neg-two*`. `lib` is the
Arithmetic library. Terms and Steps use the forms in `prover/sig/proof.md`.
`integers` is a list of integer evidence Steps in argument order. A result of
`(cons value lib)` includes the Library's resulting entries and facts in
insertion order. All calls can return a failure.

| Call | Result |
|---|---|
| `(t2-half-magnitude-distinct lib term constant distinct integers)` | A Step proving the magnitude of `term` differs from `constant`, given a Step `distinct` comparing `term` to the negated constant. |
| `(t2-half-magnitude-greater-than-two lib negative one-distinct two-distinct integers)` | A Step proving that the magnitude exceeds two. The Steps prove negativity and distinctness from minus one and minus two. |
| `(t2-half-doubled lib value integers)` | A Step equating twice the term `value` with its sum with itself. |
| `(t2-half-rounding-bound lib cross pos-factor wide integers)` | `(cons step lib)`, proving the rounding bound from the cross product equality and the indicated strict bounds on the factor and dividend. |
| `(t2-half-negated-count lib positive-value integers)` | `(cons step lib)`, equating the count of a negated positive integer with its magnitude. `positive-value` proves positivity. |
| `(t2-half-count-after lib equation count-value)` | A Step composing the given equation under `ACL2-COUNT` with the Step `count-value`. |
| `(t2-half-floor-at-minus-two lib)` | A Step proving count descent for the floor of minus two divided by two. |
| `(t2-half-negative-halving lib strict wide integers)` | `(cons step lib)`, proving descent for a negative dividend whose magnitude exceeds two, given Steps `strict` and `wide`. |
| `(t2-half-build-halving lib)` | Library with the signed floor count decrease lemma. |
| `(t2-half-signed-floor-decrease lib value divisor hypotheses)` | `(cons (list step hypotheses) lib)`, proving count descent for the term `value` and the quoted term `divisor`. |

`(t2-half-signed-floor-decrease-query lib value divisor hypotheses replies)`
also accepts the replies of `descent-query-recipe` from `prover/sig/descent.md`.
It can return a descent request as well as a failure or the result above. The
call without `replies` uses shared Hypotheses, as does a query with `:plain`
replies.

In the ordinary entry point and with `:plain` replies, the hypothesis
argument can also be a RulerFacts context from `prover/t2/sig/guarded-selectors.md`.
The resulting hypothesis context has the same form as its input.
