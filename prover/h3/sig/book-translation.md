# Floor and remainder translation

A Library and a Step have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. A term is a frozen prover term. `context` is the Bounds
object of `prover/h3/sig/book-order.md`. Evidence supplied as a list stays in
argument order. Evidence read from Bounds is taken in insertion
order.

| Call | Arguments and result | Failure |
|---|---|---|
| `(h3-book-translation-sum-equality library first second evidence)` | Terms `first` and `second`, then a list of evidence Steps. Returns `(cons step library)` with the equality of the terms and the Library with the sum lemmas. Use `nil` for omitted evidence. | `unproved` for different normalized sums, or a failure from proof construction. |
| `(h3-book-translation-sum-ratio library first second divisor)` | Two summand terms and a divisor term. Returns the Step distributing the reciprocal across the sum. | A failure from proof construction. |

A failure takes the place of the entire result. When present, the Library in a
result includes entries in the order they were added.

`(h3-book-translation-modulus-translation-with-library library formula)` and
`(h3-book-translation-modulus-scaling-with-library library formula)` take the
same arguments as the corresponding tactics. Each returns
`(cons result library)`. If a proof attempt failures after adding lemmas,
`result` contains the failure and the Library retains those lemmas. Use these
forms when handling a failure and continuing to the next tactic.
