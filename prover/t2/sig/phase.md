# Weighted and two-phase measures

`lib` is the Arithmetic library. Terms and Steps use the forms in
`prover/sig/proof.md`. A result of `(cons value lib)` includes the Library's
resulting entries and facts in insertion order. All calls can return a failure.

| Call | Result |
|---|---|
| `(t2-phase-weighted-measure term)` | `(factor size upper-phase-p)` for a recognized measure, or `nil`. The factor is a quoted integer, the size is a count or a length term, and `upper-phase-p` is Boolean. |
| `(t2-phase-weighted-ordinal lib measure)` | `(cons step lib)`, proving that the measure is an ordinal. |
| `(t2-phase-phase-separation lib child parent factor descent)` | `(cons step lib)`, proving that the upper phase for the child size is below the lower phase for the parent size. `child`, `parent` and `factor` are terms. `descent` proves strict comparison of the sizes. |
| `(t2-phase-weighted-decrease lib goal hypotheses)` | `(cons (list step hypotheses) lib)`, proving the ordinal comparison term `goal`. |

`(t2-phase-weighted-decrease-query lib goal hypotheses replies)` also accepts
the replies of `descent-query-recipe` from `prover/sig/descent.md`. It can return a
descent request as well as a failure or the result above. The call without
`replies` uses shared Hypotheses, as does a query with `:plain` replies.

`(t2-phase-hypotheses-lookup hypotheses term replies)` returns `(cons step
hypotheses)` using the Arithmetic hypothesis rules. The Step can be `nil`.
`(t2-phase-hypotheses-require hypotheses term replies)` requires a Step.
Either call can return a failure or a descent request.

In the ordinary entry point and with `:plain` replies, the hypothesis
argument can also be a RulerFacts context from `prover/t2/sig/guarded-selectors.md`.
The resulting hypothesis context has the same form as its input.

`(t2-phase-hypotheses-after-library context initial lib)` returns the context
with the resulting Library when its proof was the input Library `initial`.
It cannot fail.
