# Subtraction and count descent

`lib` is the Arithmetic library. Terms and Steps use the forms in
`prover/sig/proof.md`. A result of `(cons value lib)` includes the Library's
resulting entries and facts in insertion order. All calls can return a failure.

| Call | Result |
|---|---|
| `(t2-subtraction-nonnegative-difference lib bound)` | A Step proving a difference nonnegative, given a Step `bound` proving the weak order of its operands. |
| `(t2-subtraction-count-subtraction lib int-whole int-part positive-part bound)` | `(cons step lib)`, proving a count decrease. The four Steps prove integrality of the whole and part, positivity of the part and the weak bound of the part by the whole. |
| `(t2-subtraction-nfix-nonzero lib value distinct)` | `(cons (list integral positive-value) lib)`. `value` is the input term and `distinct` proves the result of `NFIX` is nonzero. |
| `(t2-subtraction-ifix-comparison lib whole part positive-part int-part bound)` | `(cons (list int-whole unfixed-bound) lib)`. `whole` and `part` are terms, and the Steps prove positivity and integrality of `part` and that it is at most the `IFIX` of `whole`. |
| `(t2-subtraction-subtraction-decrease lib whole part hypotheses)` | `(cons (list step hypotheses) lib)`, proving the count decrease from subtraction of term `part` from term `whole`. |

`(t2-subtraction-subtraction-decrease-query lib whole part hypotheses replies)`
also accepts the replies of `descent-query-recipe` from `prover/sig/descent.md`.
It can return a descent request as well as a failure or the result above. The
call without `replies` uses shared Hypotheses, as does a query with `:plain`
replies.

In the ordinary entry point and with `:plain` replies, the hypothesis
argument can also be a RulerFacts context from `prover/t2/sig/guarded-selectors.md`.
The resulting hypothesis context has the same form as its input.
