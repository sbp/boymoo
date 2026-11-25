# Closed evaluation

The `p` argument is the Library with the proof operations in
`prover/h4/sig/tactics.md`. Terms and Steps have the forms in
`prover/sig/proof.md`. A ClosedEvaluation has the form
`(:h4-closed-evaluation p constructor)`. The constructor field is the
reduction provider prepared by `h4-book-finite-reduction-provider`. The
accessors `h4-book-evaluation-closed-evaluation-p` and
`h4-book-evaluation-closed-evaluation-constructor` return its fields.

| Function | Arguments in order | Result | Failure |
|---|---|---|---|
| `h4-book-evaluation-closed` | Term | Whether every argument is closed, treating quotes as closed and free atoms as open. | None on terms. |
| `h4-book-evaluation-closed-evaluation-init` | `p` | ClosedEvaluation with its constructor provider. | From preparing the provider. |
| `h4-book-evaluation-closed-evaluation-unfold-spine` | ClosedEvaluation, call term | Equality Step opening the first list step, or `nil` when the call has no such step. | From term operations, normalization or proof construction. |
| `h4-book-evaluation-closed-evaluation-reduce` | ClosedEvaluation, term | Equality Step for normalization with the constructor and spine reductions. | From normalization or proof construction. |
| `h4-book-evaluation-closed-evaluation-prove` | ClosedEvaluation, formula term | Step proving the formula if it reduces to a non-nil quotation. | `inapplicable-term` when normalization leaves the required truth value unproved. Other failures can come from evaluation or proof construction. |
| `h4-book-evaluation-closed-goal` | Formula term | Whether the formula is an equality or conditional that is closed and fits the size limit. | From the term size check. |
| `h4-book-evaluation-closed-proof` | `p`, formula term | Step, or `nil` for an inapplicable goal or one of the fallback kinds in `prover/h4/notes/failures.md`. | Other failures from closed evaluation, or a failure from the goal test. |

The constructor field stores the CONSP-of-CONS equality Step used by the
reduction provider. `*h4-book-evaluation-tail*` is the symbol for the
unopened suffix. `(h4-book-evaluation-closed-evaluation-reduce-provide call
evaluation)` returns the first applicable constructor or spine reduction
Step for the call, `nil` if neither applies, or a failure.
