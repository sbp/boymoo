# Theorem recipes

`library` is a Library as described in `prover/sig/library.md`. The theorem
name and formula are a symbol and a term as described in `prover/sig/proof.md`.

| Call | Result | Failure |
|---|---|---|
| `(b2-next-recipes-prove-new-theorem library name formula)` | `(cons step library)` with a Step proving `formula` and the resulting Library. | A failure from the selected recipe or the final proof search. |

`*b2-next-recipes-keyword-theorems*` is the set of association-keyword
theorem symbols, listed in ascending order of their serialized forms.
