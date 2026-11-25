# Book proof recipes

A candidate comes with the facts named by its proof entries. The book
prover can reuse the candidate when those facts still have the same
clauses. The proof entries keep their dependency order.

The structural theorem tactic calls `t2-tree-rebalance-prove-attempt`.
An `unproved` response carries the resulting Library so that rule search
can use any lemmas installed during the attempt. When a recipe returns a
failure as its entire result, the caller has the Library it supplied to
that recipe.

`t2-books-statement-prover-generate-with-prepared-rules` takes a prepared
rule index for theorem and equational witness searches.
