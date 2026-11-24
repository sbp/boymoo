# Floor and remainder translation

A Library and a Step have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. A term is a frozen prover term. `context` is the Bounds
object of `prover/h3/sig/book-order.md`. Evidence supplied as a list stays in
argument order. Evidence read from Bounds is taken in insertion
order.

| Call | Arguments and result | Failure |
|---|---|---|
| `(h3-book-translation-sum-equality library first second evidence)` | Terms `first` and `second`, then a list of evidence Steps. Returns `(cons step library)` with the equality of the terms and the Library with the sum lemmas. Use `nil` for omitted evidence. | `Unproved` for different normalized sums, or a failure from proof construction. |
| `(h3-book-translation-sum-ratio library first second divisor)` | Two summand terms and a divisor term. Returns the Step distributing the reciprocal across the sum. | A failure from proof construction. |
| `(h3-book-translation-mod-translate library base delta divisor notzero context)` | Original dividend term, displacement term, Step proving the divisor rational, Step proving it nonzero, and Bounds. Returns `(cons step library)` with the equality of the displaced and original remainders and the resulting Library. | A failure from proof construction or search. |
| `(h3-book-translation-product-remainder library call factor)` | A remainder call and the factor term in its dividend product. Returns `(cons step library)` with the equality to a scaled remainder and the resulting Library. | A failure from proof construction. |
| `(h3-book-translation-modulus-translation library formula)` | Formula term. Returns `(cons step library)` with the implication proved by translation and the resulting Library. The Step is `nil` when there is no proof. | A failure from proof construction or search. |
| `(h3-book-translation-modulus-scaling library formula)` | Formula term. Returns `(cons step library)` with the equality to a scaled remainder or zero, including any implication guard, and the resulting Library. The Step is `nil` when the formula does not match. | A failure from proof construction or search. |

A failure takes the place of the entire result. When present, the Library in a
result includes entries in the order they were added.

`(h3-book-translation-modulus-translation-with-library library formula)` and
`(h3-book-translation-modulus-scaling-with-library library formula)` take the
same arguments as the corresponding tactics. Each returns
`(cons result library)`. If a proof attempt failures after adding lemmas,
`result` contains the failure and the Library retains those lemmas. Use these
forms when handling a failure and continuing to the next tactic.
