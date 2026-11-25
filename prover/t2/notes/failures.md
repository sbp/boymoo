# Failure kinds

T2 returns `(:failure "failure" "")` when a failure has no special
handling. `fuel` identifies the recursion that exhausted its counter.
The other T2 kinds have empty messages.

`t2-api-engine-guess-measure`, `t2-api-engine-generate`,
`t2-api-engine-prove-target`, `t2-api-engine-retry`, `t2-open-prove-target`
and `t2-open-retry` test the five kinds in the table. The result determines
whether a proof attempt can be repeated with a different measure or
additional lemmas. `t2-books-failure-kind-p` performs these tests.
`t2-hints-discard-instance-p` tests `recipe-mismatch` and `missing-term-part`
for `t2-hints-instance`. The predicates also accept the shared kinds
specified in `prover/FAILURES.md` where those failures have the same recovery.
