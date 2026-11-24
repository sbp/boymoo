# List size bounds

`proof` is an H1 Prover. Terms and Steps have the forms in
`prover/sig/proof.md`. A list bound is a Step proving a weak or strict
comparison.

| Call | Result | Failure |
|---|---|---|
| `(h1-book-list-size-counting term)` | The `ACL2-COUNT` application to `term`. | — |
| `(h1-book-list-size-length term)` | The `LEN` application to `term`. | — |
| `(h1-book-list-size-align-comparison proof desired known)` | A Step equating the two strict comparison terms by aligning their differences. | A failure from proof construction. |
| `(h1-book-list-size-shifted-bound proof comparison original)` | The bound Step `original` transported to the comparison term `comparison`. | A failure from proof construction. |
| `(h1-book-list-size-sum-of-bounds proof target first second)` | A weak bound Step for `target`, using the two bound Steps in argument order. | A failure from proof construction. |
| `(h1-book-list-size-count-nonnegative proof term)` | A Step proving `ACL2-COUNT` of `term` nonnegative. | A failure from proof construction. |
| `(h1-book-list-size-length-positive proof cons)` | A Step proving `LEN` positive for the term in the `CONSP` Step `cons`. | A failure from proof construction. |
| `(h1-book-list-size-list-size-induction proof)` | The induction Step for the list size invariant. | A failure from proof construction. |
| `(h1-book-list-size-install-length-zero proof)` | The Prover with the zero-length formulas installed. | A failure from proof construction. |
| `(h1-book-list-size-install-count-bounds proof)` | The Prover with the size bounds installed. | A failure from proof construction. |
| `(h1-book-list-size-install-list-sizes proof)` | The Prover after the length and size bounds are installed in that order. | A failure from proof construction. |

The constants `*h1-book-list-size-nth*`, `*h1-book-list-size-true-list*`
and `*h1-book-list-size-two*` are the symbols `COMMON-LISP::NTH` and
`ACL2::TRUE-LISTP`, and quoted `2`, respectively.

`(h1-book-list-size-step-at step place)` indexes a Step's first literal
using the list of zero-based indices `place`. Negative positions count
from the end of the term. An empty `place` returns the literal. Reading
the Step or term can return a failure.

`(h1-book-list-size-list-size-induction-fold bound length-position proof count-eq length-eq)`
folds the size and length equalities into the bound at the indicated
positions. `(h1-book-list-size-list-size-induction-selection-bound equation method old-bounds proof actual-size actual-length count-eq length-eq)`
folds the selected element's bound. `method` is `:shifted-bound` or
`:sum-of-bounds`, and `old-bounds` supplies that method's Steps in order.
These functions return a Step or a failure.

`(h1-book-list-size-simplify proof term evidence definitions)` runs the
simplifier with the H1 constant rules. The result is a simplification
Step, `nil` for an unchanged term, or a failure.
