# Affine countdown proofs

Terms and Steps have the forms in `prover/sig/proof.md`. The `proof` argument is the H2 proof object. `evidence`, `facts` and `assumptions` are lists of Steps in the order supplied to the call. A failure, when propagated, is the entire result.

| Call | Result |
|---|---|
| `(h2-ranges-conjuncts proof evidence)` | The list of Steps yielded by projecting the conjunction Step `evidence`, left to right, including the last conjunct. May propagate a failure from a projection. |
| `(h2-ranges-difference-positive proof lower upper comparison evidence)` | A Step proving that the difference of the two endpoint terms is positive, given the strict comparison Step and integer evidence. May propagate a failure. |
| `(h2-ranges-positive-span proof span facts)` | A Step proving that the integer span term is positive, or `nil` when no comparison Step aligns with it. May propagate a failure. |
| `(h2-ranges-numeric-fixer proof term)` | An equality Step aligning the book's `NFIX` application with the natural fix of the arithmetic lemmas. May propagate a failure. |
| `(h2-ranges-affine-decrease proof goal assumptions)` | The Step proving the ordinal decrease `goal` from the ordered assumptions, or `nil` when this tactic does not apply. May propagate a failure. |

`*h2-ranges-book-nfix*` is the prover symbol for `ACL2::NFIX`.

`conjuncts` and `numeric-fixer` also accept a plain Proof or Library.
