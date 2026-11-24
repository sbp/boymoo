# Structural proofs for lists and lookup

`proof` is the H1 Prover defined by `tactics`. Terms and Steps use the forms
in `prover/sig/proof.md`. `tests` is an ordered list of `(term holds)` pairs,
with `t` for a true test and `nil` for a false test.

| ACL2 call | Result | Failure |
|---|---|---|
| `(h1-book-structure-container-case proof application known)` | A Step unfolding list function term `application` and selecting its atom or cons branch using Step `known`. | `Unproved` if there is no matching branch, or a failure from proof construction. |
| `(h1-book-structure-projected-association proof formula)` | A Step proving term `formula`, an implication relating a recognizer on a projected list to a recognizer on an association result. | `Unproved` if the required definition or branch shape is absent, or a failure from proof construction. |
| `(h1-book-structure-nonempty-first-row proof root tests cons-evidence)` | A Step proving the first row of term `root` is a cons, with the given branch tests and Step `cons-evidence` proving `root` a cons. | `Unproved` if no matching emptiness test is found, or a failure from proof construction. |
| `(h1-book-structure-first-row-descent proof variable actual tests)` | A Step proving ordinal descent of the first row when symbol `variable` advances to term `actual` under the given branch tests. | `Unproved` if `actual` does not have the required first-row equation, or a failure from proof construction. |
| `(h1-book-structure-tuple-induction proof formula)` | A Step proving term `formula` by induction on the size of a first row. | `Unproved` if no first-row induction succeeds, or a failure from proof construction. |

Failures replace the entire result. The constants `*h1-book-structure-atom*`
and `*h1-book-structure-endp*` denote the Common Lisp predicate symbols.
`*h1-book-structure-strip*` is the dictionary from `CAR` to `STRIP-CARS`
then `CDR` to `STRIP-CDRS`, in that insertion order.
`*h1-book-structure-lookup*` lists `ASSOC-EQUAL` then `HONS-ASSOC-EQUAL`.
Tuple induction visits formula subterms, arguments, and recursive substitutions
in the order of their first occurrence.
