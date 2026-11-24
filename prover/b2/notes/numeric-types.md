# Type propagation

A Types record retains the Search index created at initialization, the
current Library, the set of visited terms, and the remaining type-search
budget. Type proofs carry the Library with their supporting lemmas. The
theorem entry can pass that Library to a subsequent proof attempt.

`grep -nE 'b2-numeric-types-types-(init|with-library)|b2-next-recipes-prove-new-theorem-type' prover/b2/numeric-types.lisp prover/b2/next-recipes.lisp` shows the proof operations. The command was run on 2026-11-23.
