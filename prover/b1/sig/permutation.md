# Permutation

| Call | Arguments and result | Failure |
|---|---|---|
| `(b1-permutation-permutation-is-equivalence lib formula)` | Library and the conjunction term of the Boolean-valuedness, reflexivity, symmetry and transitivity of `PERM`, in that order. Returns `(cons step lib)` with the Step for the formula and the Library carrying its auxiliary lemmas in insertion order. | A failure from reading a term or constructing a proof. |
