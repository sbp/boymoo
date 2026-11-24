# Character-list results

`lib` is a Library as specified in `prover/sig/library.md`. Terms and Steps
have the forms in `prover/sig/proof.md`. `evidence` is an Evidence object
as specified in `prover/t3/sig/logic.md`. The optional theorem Step is
`nil` when its tactic does not apply.

| Call | Result | Failure |
|---|---|---|
| `(t3-book-character-lists-packed-characters lib name formula)` | `(cons entry lib)` with the proof entry for the named packed-character theorem and the Library extended by the auxiliary lemmas. `name` is the theorem symbol and `formula` its statement term. | A failure from proof construction or theorem selection. |
| `(t3-book-character-lists-element-list lib predicate element-type value evidence)` | A Step proving `(predicate value)` for the constructed list term `value`. `predicate` and `element-type` are recognizer symbols. | `Unsupported` if there is no result rule, or a failure from proof construction. |
| `(t3-book-character-lists-preserving-elements lib formula)` | `(cons step lib)` with the optional Step for the statement term and the Library after adding any character-list append lemma. | A failure from inspecting the statement or constructing its proof. |

`*t3-book-character-lists-explode-atom*`, `*t3-book-character-lists-pack-list*`,
`*t3-book-character-lists-pack-tree*`, and `*t3-book-character-lists-string-list*`
are the symbols for `EXPLODE-ATOM`, `PACK-LIST`, `PACK-TREE`, and
`STRING-LISTP`. A proof entry has the form returned by
`proof-proof-entry`. Structural induction substitutions retain the order of
the first visit to each recursive child term.
