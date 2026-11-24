# Sorted-list theorems

`lib` is a Library as specified in `prover/sig/library.md`. Terms and Steps
have the forms in `prover/sig/proof.md`. A proof entry has the form returned
by `proof-proof-entry`.

| Call | Arguments | Result | Failure |
|---|---|---|---|
| `(t3-book-sorted-lists-ordered-perms lib name formula)` | Library, theorem symbol, statement term | `(cons entry lib)` with the sorted-permutation theorem entry and the Library extended by its auxiliary lemmas. | A failure from statement inspection or proof construction. |
| `(t3-book-sorted-lists-ordered-sort lib name formula)` | Library, theorem symbol, statement term | `(cons entry lib)` with the merge-sort order theorem entry and the Library extended by its auxiliary lemmas. | A failure from proof construction. |

`*t3-book-sorted-lists-ordered*` is the symbol for `TERM-ORDEREDP`.
`*t3-book-sorted-lists-true-listp*` is the `TRUE-LISTP` symbol from
`book-lemmas`.
