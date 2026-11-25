# Numeric termination measures

`p` is the Library used by H4 Tactics. Terms and Steps have the forms in
`prover/sig/proof.md`. Definitions and Calls have the forms in
`prover/sig/termination.md`. `support` is an ordered fact map from names to
clauses. `evidence` is an association list from first literals to Steps.
When a key recurs in an evidence or proof map, its new value replaces the
old value at the same position.

A successful measure result is `(measures proofs)`, where `measures` is the
list of measure terms in definition order and `proofs` is the list of Steps
in obligation order. A tactic that does not apply returns `nil` as the
measure result.

| Function | Arguments and result | Failure |
|---|---|---|
| `(h4-book-numeric-measures-numeric-termination p definitions calls support)` | Try subtraction, increasing index and division in order. Returns `(cons result library)`, including the installed division facts and a `nil` result for the division fallback kinds in `prover/h4/notes/failures.md`. | Other failures propagate. |
| `(h4-book-numeric-measures-uses-floor-measure calls)` | Return `t` when the Call list has a common argument position updated by floor or unary rounding of a ratio with a quoted base greater than one, and `nil` otherwise. | May propagate a malformed-term failure from `floor-parts`. |
| `(h4-book-numeric-measures-signed-countdowns p call)` | Return the evidence map for the Call's tests in the order yielded by `h4-book-measures-rule-tests`. | May return a failure. |
| `(h4-book-numeric-measures-positive-integer p term evidence)` | Return the integer and positive Steps for `term`, in that order, from countdown evidence. | May return a failure. |
| `(h4-book-numeric-measures-subtraction-measure p definitions calls)` | Return the measure result for subtraction, with proofs in first-occurrence clause order. | May return a failure. |
| `(h4-book-numeric-measures-floor-parts term)` | Return `(value base)` from a recognized rounding term or `nil`. | May return a failure on a malformed application. |
| `(h4-book-numeric-measures-floor-view p actual value base integers)` | Return a Step equating the actual term to its floor form by using value and base terms and integer evidence Steps. | May return a failure. |
| `(h4-book-numeric-measures-fixed-value-type p call)` | Return one natural-number Step for an `NFIX` term, or the list of the integer and positive Steps for a positive-fix term. | May return a failure. |
| `(h4-book-numeric-measures-increasing-index-measure p definitions calls)` | Return the increasing-index measure result. | May return a failure. |
