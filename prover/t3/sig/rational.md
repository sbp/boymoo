# Rational component bounds

`lib` is a Library from `prover/sig/library.md`. Terms and Steps use the forms in `prover/sig/proof.md`. `evidence` is a T3 Evidence object from `prover/t3/sig/logic.md`. Any failure is the entire result.

The symbol constants are `*t3-rational-abs*`, `*t3-rational-numerator*`, `*t3-rational-denominator*` and `*t3-rational-reciprocal*`.

| ACL2 call | Result | Failure |
|---|---|---|
| `(t3-rational-product-zero lib)` | Library with the product-by-zero lemma. | A failure from proof or lemma construction. |
| `(t3-rational-abs-facts lib)` | Library with integrality and positivity lemmas for integer absolute value, in that order. | A failure from proof or lemma construction. |
| `(t3-rational-count-branch lib term rational integral)` | Equality Step simplifying the count of `term` using Steps `rational` and `integral` for its rationality and signed integrality. | A failure from proof construction. |
| `(t3-rational-rational-counts lib)` | Library with product and absolute value lemmas followed by strict count bounds for numerator and denominator, in that order. | A failure from proof or lemma construction. |
| `(t3-rational-rational-descent lib smaller larger evidence)` | `(cons step (cons library evidence))` with the updated Library and Evidence after proving a component decrease from count terms `smaller` and `larger`. The step is `nil` when inapplicable. | A failure from reading terms, proof construction or missing evidence. |

The simplification rules are selected by the Library class through `t3-book-spines-library-simplify`. For `count-branch`, `lib` can also be a book proof context carrying its package declarations.
