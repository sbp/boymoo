# Membership in a list of typed elements

`p` is the H4 Tactics library. Formulas and Steps use the representations in `prover/sig/proof.md`. The constants `*h4-book-list-types-member*` and `*h4-book-list-types-synp*` are the prover symbols `MEMBER-EQUAL` and `SYNP`.

| Call | Result | Failure |
|---|---|---|
| `(h4-book-list-types-conjuncts formula)` | List of conjunct formulas, visiting the test before the true branch of each `(IF test branch 'NIL)`. | A failure on a truncated `IF`. |
| `(h4-book-list-types-conjunct-proofs p step)` | List of Steps for the conjuncts of the first literal, in the same order as `conjuncts`. | A failure from reading or splitting a Step. |
| `(h4-book-list-types-membership-induction p member list-test goal)` | Step for the implication from membership and the list predicate to the item predicate `goal`. | A failure from proof construction. A failed proof condition can produce `inapplicable-step`. |
| `(h4-book-list-types-member-type-proof p formula)` | Step for `formula`, or `nil` when there is no successful match. | A failure from matching or proof construction. An `inapplicable-step` during induction advances to the next match. |
