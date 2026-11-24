# Ordering and sign proofs

`proof` is the H1 Prover defined by `tactics`. `normalizer` is the Algebra
defined by `book-arithmetic`, and `context` is the Context defined by `tactics`.
Terms and Steps use the forms in `prover/sig/proof.md`. The symbol constants
`*h1-book-order-booleanp*` and `*h1-book-order-rationalp*` denote `ACL2::BOOLEANP`
and `COMMON-LISP::RATIONALP`.

| ACL2 call | Result | Failure |
|---|---|---|
| `(h1-book-order-rational value)` | The `RATIONALP` application to term `value`. | — |
| `(h1-book-order-product a b)` | The binary product of terms `a` and `b`. | — |
| `(h1-book-order-positive-sum proof left right first second)` | A Step proving the sum of terms `left` and `right` positive, from Steps `first` and `second`. | A failure from proof construction. |
| `(h1-book-order-by-difference proof left right normalizer)` | `(cons step normalizer)` with the Step identifying comparison terms `left` and `right` and the resulting Algebra. | `Unproved` or a failure from normalization or proof construction. |
| `(h1-book-order-boolean-value proof known)` | A Step for the exact Boolean value of the order literal proved by Step `known`. | A failure from proof construction. |
| `(h1-book-order-nonzero-from-sign proof signed value)` | A Step proving term `value` nonzero from the sign Step `signed`. | A failure from proof construction. |
| `(h1-book-order-install-signs proof)` | The Prover with the Boolean and rational sign lemmas installed in order. | A failure from normalization or proof construction. |
| `(h1-book-order-install-boolean-equality proof)` | The Prover with `BOOLEAN-EQUALITY-IFF` and the `booleanp-` fact rules installed. | A failure from proof or rule construction. |
| `(h1-book-order-boolean-equality proof formula)` | A Step equating equality with equivalence for the Boolean arguments in term `formula`. | `Unproved` when the formula or evidence is insufficient, or a failure from proof construction. |
| `(h1-book-order-scale-sign proof)` | A Step showing that multiplication by a positive rational preserves the sign. | A failure from normalization or proof construction. |
| `(h1-book-order-install-integer-successor-bound proof)` | The Prover with `SUCCESSOR-WEAK-BOUND` installed. | A failure from normalization or proof construction. |
| `(h1-book-order-install-order proof)` | The Prover with the sign, Boolean, successor, and scaling lemmas and rules installed in order. | A failure from normalization, proof, or rule construction. |
| `(h1-book-order-add-signed-evidence proof normalizer)` | The resulting Algebra, with sign and zero evidence added to its Context. | A failure from a lookup or proof construction. |
| `(h1-book-order-comparison-factors left right context)` | Distinct scaling factors for the comparison terms `left` and `right`, in first-occurrence order. | — on comparison terms. |
| `(h1-book-order-compare-orders proof left right normalizer)` | `(cons step normalizer)` identifying two comparison terms and returning the resulting Algebra. | `Unproved` if no alignment is found, or a failure from lookup, normalization, or proof construction. |
| `(h1-book-order-scaled-orders proof source factors context)` | `(cons steps context)` with the Steps for scaling comparison term `source` by the given factor terms and the resulting Context. The Steps follow the order of the factors. | A failure from lookup or proof construction. |
| `(h1-book-order-computed-order proof step normalizer)` | `(cons step normalizer)` with the computed comparison equality Step, or `nil` as the value when the comparison cannot be computed. The input `step` is an equality with a comparison on the right. | A failure from normalization or proof construction. |
| `(h1-book-order-compare-value proof order value normalizer)` | `(cons step normalizer)` with a Step equating comparison term `order` to quoted Boolean term `value` and the resulting Algebra. | `Unproved` if no proof is found, or a failure from lookup, normalization, or proof construction. |

For results specified as pairs, a failure occupies the value position so that
the caller has the resulting Algebra or Context after a failed attempt.
The other calls return a failure directly. Context evidence and the temporary
dictionaries of denied signs keep insertion order. Replacing evidence for an
existing literal keeps its position. The comparison routines visit scaled
orders only as needed and keep evidence from each attempted factor.
