# Set equivalence proofs

`p` is the H4 Tactics library. Terms and Steps use the representations in `prover/sig/proof.md`. The prover symbols are `*h4-book-sets-member*` (`MEMBER-EQUAL`), `*h4-book-sets-subset*` (`SUBSETP-EQUAL`), `*h4-book-sets-set-equiv*` (`SET-EQUIV`), `*h4-book-sets-boolean*` (`BOOLEANP`) and `*h4-book-sets-item*` (`A`). A `shape` is a Step specifying the cons or atom case of the sequence in question. All the proof functions can return a failure from reading terms or constructing a proof.

| Call | Result |
|---|---|
| `(h4-book-sets-nonempty-value p shape)` | Step that the subject of the `CONSP` Step `shape` is true as a value. |
| `(h4-book-sets-subset-parts p step shape)` | Two-element list of Steps for the member head and included tail of the subset Step `step`. |
| `(h4-book-sets-head-member p sequence shape)` | Step that the head of `sequence` is a member of `sequence`. |
| `(h4-book-sets-member-extension p head tail membership)` | Step extending the membership of an item in `tail` to membership in `(CONS head tail)`. |
| `(h4-book-sets-subset-extension p)` | Step for subset inclusion after adding an element to the right-hand list. |
| `(h4-book-sets-transfer-membership p)` | Step for transferring membership across subset inclusion. |
| `(h4-book-sets-subset-transitivity p)` | Step for transitivity of subset inclusion. |
| `(h4-book-sets-select-equal p selector equality)` | Step applying `selector` to the two cons terms in the equality Step. |
| `(h4-book-sets-subset-of-equal-fixes p)` | Step deriving subset inclusion from equality of the list fixes. |
| `(h4-book-sets-boolean-result p equation induction)` | Step that the left side of the equality Step `equation` is Boolean. `induction` is a Step available for the recursive value, or `nil`. |
| `(h4-book-sets-boolean-subset p)` | Step that subset inclusion produces a Boolean. |
| `(h4-book-sets-set-pair p left right)` | Step combining the two subset Steps into set equivalence. |
| `(h4-book-sets-set-parts p step)` | Two-element list of the subset Steps obtained from a set equivalence Step. |
| `(h4-book-sets-set-equivalence p)` | Step for the conjunction of Boolean typing, reflexivity, symmetry and transitivity. |
| `(h4-book-sets-set-refinement p formula)` | Step that list equivalence implies set equivalence, in the form of `formula`. |
| `(h4-book-sets-set-shape formula)` | Boolean recognizing the list equivalence refinement or the set equivalence conjunction. May return a failure on a malformed formula. |
| `(h4-book-sets-set-proof p formula)` | Step for `formula`, or `nil` when the tactic is inapplicable, a proof assertion fails, or the resulting first literal differs from `formula`. |
