# Lexicographic ordinal embedding

`library` is a Library as described in `prover/sig/library.md`. Lexicographic uses the Library representation and the inference methods of Ordinals. Steps and terms have the forms in `prover/sig/proof.md`. A Call has the form in `prover/sig/termination.md`.

The constants `*t4-lexicographic-encode*`, `*t4-lexicographic-fix*`, `*t4-lexicographic-fix-list*`, `*t4-lexicographic-lex-fix*`, `*t4-lexicographic-lex-type*`, `*t4-lexicographic-nat-list*`, `*t4-lexicographic-l-less*`, `*t4-lexicographic-d-less*`, and `*t4-lexicographic-do*` name the embedding and its operators.

Every function in the table can return a failure. Library results retain definitions and proof entries in their order of construction. A binding is a two-element list of a symbol and a term.

| ACL2 call | Result |
|---|---|
| `(t4-lexicographic-conjunction terms)` | The terms joined by right-associated conditionals, in order. returns a failure for an empty argument list. |
| `(t4-lexicographic-lexicographic-build-embedding library)` | Library with the embedding definition, measure and lemmas. |
| `(t4-lexicographic-lexicographic-do-descent library goal call)` | Step proving the strict ordinal comparison `goal` using the first positive `L<` test in `call`. |
| `(t4-lexicographic-lexicographic-encodings library)` | Library with the definition, its measure and the lemmas about its leading exponent and ordinality. |
| `(t4-lexicographic-lexicographic-fix-list-type library)` | Library with `LEX-FIX-LIST-TYPE`. |
| `(t4-lexicographic-lexicographic-fix-type library)` | Library with `LEX-FIX-TYPE`. |
| `(t4-lexicographic-lexicographic-digit-order library)` | Library with `LEX-DIGIT-ORDER` and the auxiliary lemmas used to prove it. |
| `(t4-lexicographic-lexicographic-lex-order library)` | Library with `LEX-ORDER` and the auxiliary lemmas used to prove it. |
| `(t4-lexicographic-lexicographic-branch-value library term test-proof)` | Equality Step for `term` and the selected branch of its definition. |
| `(t4-lexicographic-lexicographic-length-positive library object cons-proof)` | Step that `LEN` of `object` is positive using the Step that `object` is a cons. |
| `(t4-lexicographic-lexicographic-nfix-equal library object)` | Equality Step for the two natural-number fixers applied to `object`. |
| `(t4-lexicographic-lexicographic-tail-lengths-equal library same-length cons-x cons-y)` | Equality Step for the tail lengths of the two conses with equal lengths. |
| `(t4-lexicographic-lexicographic-lex-order-transport pair left right library)` | Comparison Step transported through the two equality Steps in argument order. |
| `(t4-lexicographic-lexicographic-lex-order-impossible positive negative library claim)` | Step for `claim` under the contradictory premises of the two input Steps. |

`t4-lexicographic-nat-list-fields-with-library` and
`t4-lexicographic-lex-parts-with-library` take the arguments of the
corresponding methods. They return `(cons result library)` with any
auxiliary lemmas that were added, or a failure.
