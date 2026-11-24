# Rewriting triggers

`proof` is the H1 Prover defined in `prover/h1/sig/tactics.md`. Terms,
templates, and Steps have the forms in `prover/sig/proof.md`. The named
symbols `TRIGGER`, `FIND`, `REWRITE`, `MV_NTH`, `CONJOIN_CLAUSES`,
`DISJOIN_LIST`, and `CONJOIN` use the constants `*h1-book-trigger-trigger*`,
`*h1-book-trigger-find*`, `*h1-book-trigger-rewrite*`,
`*h1-book-trigger-mv-nth*`, `*h1-book-trigger-conjoin-clauses*`,
`*h1-book-trigger-disjoin-list*`, and `*h1-book-trigger-conjoin*`.
`*h1-book-trigger-return-last*` is `RETURN-LAST` and `*h1-book-trigger-two*`
is the quoted integer 2.

| ACL2 call | Result | Failure |
|---|---|---|
| `(h1-book-trigger-semantic-match literal old new)` | The implication from the falsity of the evaluated literal to equality of the evaluated old and new terms. | — |
| `(h1-book-trigger-tuple-parts result first-is-car)` | The three field projections from term `result`, in order. A true `first-is-car` selects `CAR` for the first projection. | — |
| `(h1-book-trigger-tuple-fields value)` | The three field terms of the constructed tuple `value`, in order. | A failure from indexing a malformed value. |
| `(h1-book-trigger-restore-tuple proof step expected value first-is-car)` | A Step with the three fields restored to their projections in template `expected`. | A failure from indexing or proof construction. |
| `(h1-book-trigger-literal-equality proof literal tests)` | A Step for the equality justified by a false evaluation of `literal` under the ordered signed `tests`. | A failure from hypothesis lookup or proof construction. |
| `(h1-book-trigger-trigger-selection proof)` | The Step for the signature of the trigger selection function. | A failure from proof construction. |
| `(h1-book-trigger-found-member proof literal endp equal tail)` | A Step for membership of `literal` in the clause. `endp` is a Step for nonemptiness. `equal` is the Step for equality to the head when known. `tail` is the Step for membership in the tail when needed. Pass `nil` for omitted Steps. | A failure from proof construction. |
| `(h1-book-trigger-find-selection proof)` | The Step for the signature of the search for a trigger. | A failure from proof construction. |
| `(h1-book-trigger-prove-rewriter proof)` | The Step for the correctness of the equality clause rewriter. | A failure from proof construction. |
| `(h1-book-trigger-install-triggers proof)` | The updated Prover with the trigger lemmas in installation order. | A failure from proof construction. |

The selection closures take the arguments below. A template marks the
result slots with `*proof-result*`. The search signature leaf uses the
induction `formula`, the `endp` test term, and the ordered `(formal actual)`
`bindings` for the recursive call.

| ACL2 call | Result | Failure |
|---|---|---|
| `(h1-book-trigger-trigger-selection-signature literal old new)` | The trigger signature formula for the given fields. | — on term inputs. |
| `(h1-book-trigger-trigger-selection-leaf value tests proof template)` | Step for the trigger signature at a result value under its signed tests. | A failure from proof construction. |
| `(h1-book-trigger-find-selection-signature literal old new)` | The search signature formula for the given fields. | — on term inputs. |
| `(h1-book-trigger-find-selection-leaf value tests proof template formula endp bindings)` | Step for the search signature at a result value, with induction for the recursive value. | A failure from proof construction. |
