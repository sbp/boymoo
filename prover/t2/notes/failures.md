# Failure kinds

T2 returns `(:failure "failure" "")` when a failure has no special
handling. `Fuel` identifies the recursion that exhausted its counter.
The other T2 kinds have empty messages.

| Kind | Meaning | Where the kind changes the result |
|---|---|---|
| `Unproved` | The tactic exhausted its search. | `t2-books-structural-theorem` and `t2-books-search-theorem` can try a different proof. `t2-tree-rebalance-unproved-p` identifies attempts that leave a usable Library. `t2-books-statement-prover-witness-with-rules` tries an equational witness. `t2-books-book-try-candidate` records the skip. |
| `Unsupported` | The recipe cannot handle the obligation or its measure. | `t2-books-statement-prover-definition-with-state`, `t2-books-statement-prover-definition-selectors` and `t2-books-statement-prover-definition-floor` select the next termination tactic or report `Unproved`. |
| `RecipeMismatch` | A proof recipe or hint fails one of its preconditions. | The definition tactics also test this kind, including `t2-books-statement-prover-definition-dyadic`. `t2-hints-instance` discards the hint, `t2-books-statement-prover-witness-with-rules` tries an equational witness, and `t2-books-book-try-candidate` records the skip. |
| `MissingBinding` | A recipe needs an absent fact, definition, measure or term binding. | The definition tactics listed above, `t2-books-statement-prover-witness-with-rules` and `t2-books-book-try-candidate` handle this kind as a failed attempt. |
| `MissingTermPart` | An application or a proof term lacks a part required by the tactic. | `t2-hints-instance` discards the hint and `t2-books-statement-prover-witness-with-rules` tries an equational witness. |

`t2-api-engine-guess-measure`, `t2-api-engine-generate`,
`t2-api-engine-prove-target`, `t2-api-engine-retry`, `t2-open-prove-target`
and `t2-open-retry` test the five kinds in the table. The result determines
whether a proof attempt can be repeated with a different measure or
additional lemmas. `t2-books-failure-kind-p` performs these tests.
`t2-hints-discard-instance-p` tests `RecipeMismatch` and `MissingTermPart`
for `t2-hints-instance`. The predicates also accept the shared kinds
specified in `prover/FAILURES.md` where those failures have the same recovery.
