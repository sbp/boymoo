# Integer bounds

`lib` is a Library with the T3 proof rules selected by its dispatch tag. `evidence`
is the Evidence from `logic.lisp`. A Step and a term have the forms given
in `prover/sig/proof.md`. `integers` is an ordered list of Steps. The constant
`*t3-arithmetic-two*` is the quotation of 2.

Evidence operations return `(cons value updated-evidence)`. Use the returned
Evidence for the next query of the same object. In these pairs, a missing
Step is `nil`. A failure is returned as the entire result. The integer fact operation takes its terms in a list.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t3-arithmetic-double term)` | The product of quoted 2 and `term`. | None. |
| `(t3-arithmetic-build lib)` | The Library extended with the four arithmetic lemmas in source order. | A failure from constructing or adding a lemma. |
| `(t3-arithmetic-coefficients term)` | Association list from atoms to nonzero integer coefficients. The constant key is `*proof-zero*`. Keys retain the order of first encounter during collection. | A failure from a malformed sum or unsupported arithmetic. |
| `(t3-arithmetic-coefficients-collect expression weight result)` | The coefficient association list `result` after collecting `expression` with integer multiplier `weight`, including zero totals until collection finishes. | A failure from a malformed sum or unsupported arithmetic. |
| `(t3-arithmetic-expand-doubles lib term integers)` | A Step equating `term` with the term whose doubles are expanded, or `nil` if unchanged. | A failure from proof construction or a malformed sum. |
| `(t3-arithmetic-linear-identity lib left right integers)` | A Step equating `left` and `right` by expanding and reducing their sums. | `Unsupported` for different normal forms, or a failure from proof construction. |
| `(t3-arithmetic-linear-identity-reduced n term opened lib integers)` | Normalize `term` from equality Step `opened`, or from reflexivity if `opened` is `nil`. Pass `1000000` as the initial fuel `n`. | `Fuel` or a failure from proof construction. |
| `(t3-arithmetic-integer-facts evidence terms)` | Pair containing the list of known and inferred integer Steps and the resulting Evidence. Known Steps are visited in fact insertion order. Inferred atoms are visited in the order of their written terms. | A failure from evidence or proof construction. |
| `(t3-arithmetic-positive-atom evidence atom)` | Pair containing a proof that `atom` is positive, if found, and the resulting Evidence. | A failure from evidence or proof construction. |
| `(t3-arithmetic-add-positive lib strict weak integers)` | A Step for the sum of the positive and nonnegative terms proved by `strict` and `weak`. | A failure from reading or constructing a Step. |
| `(t3-arithmetic-positive-difference lib target evidence integers)` | Pair containing the first positive decomposition Step for `target` and the resulting Evidence. | `Unsupported` when no decomposition works, or a failure from evidence or proof construction. |
| `(t3-arithmetic-integer-comparison lib left right evidence)` | Pair containing a strict comparison Step for `left < right` and the resulting Evidence. | A failure from evidence, proof construction, or decomposition. |
| `(t3-arithmetic-clipped-descent lib smaller larger evidence)` | Pair containing the decrease Step between the clipped measures and the resulting Evidence. | A failure from evidence or proof construction. |
| `(t3-arithmetic-gap-descent lib smaller larger evidence)` | Pair containing the decrease Step between the clipped gaps and the resulting Evidence. A derived strict endpoint fact is inserted in the Evidence in discovery order. | `Unsupported` when the endpoints differ, or a failure from evidence or proof construction. |
| `(t3-arithmetic-successor-bound lib old new limit evidence)` | Pair containing a weak comparison Step bounding the successor `new` by `limit` and the resulting Evidence. | A failure from evidence or proof construction. |

Use `t3-logic-libraryproofs-for-book` from `prover/t3/sig/logic.md` on the
Library component of a book proof context. The dispatch tag selects its
natural and integer rules for clipped terms.
