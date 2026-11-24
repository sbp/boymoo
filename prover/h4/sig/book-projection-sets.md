# Set relations on projections

`p` is the Library used for the book tactics. Terms and Steps follow
`prover/sig/proof.md`. `projection` is the function symbol for the key
or value projection. Each function can return a failure.

| ACL2 call | Result |
|---|---|
| `(h4-book-projection-sets-projected-member p equation)` | Membership Step for the head of the constructor on the right of the equality Step `equation`, in the projected list on its left. |
| `(h4-book-projection-sets-projected-membership p projection)` | Step proving that membership of an entry implies membership of its key or value in the projection. |
| `(h4-book-projection-sets-projected-subset p projection)` | Step proving that inclusion of alists implies inclusion of their projections. |
| `(h4-book-projection-sets-mapped-set-equiv p formula)` | Step proving the set equivalence of the projected lists from the set equivalence premise in `formula`. |
| `(h4-book-projection-sets-pairlis-values p formula)` | Step identifying the value projection of `PAIRLIS$` with the list fix of the values when the input lists have equal length. |
| `(h4-book-projection-sets-projection-set-proof p formula)` | A Step for a recognized set equivalence or `PAIRLIS$` formula, or `nil`. |
