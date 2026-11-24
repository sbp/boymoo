# Integer quotient and floor bounds

`lib` is a Library as in `prover/sig/library.md`. Terms, symbols and Steps
have the forms in `prover/sig/proof.md`. Names denoting variables, numeric
operands or bounds are terms unless described as Steps. `conjunction` and `combine` consume their lists from left to right.

| Call | Result |
|---|---|
| `(t4-division-conjunction terms)` | The right-associated conjunction term from the list of terms. |
| `(t4-division-pieces lib proof)` | The Steps obtained by splitting the conjunction Step from left to right. |
| `(t4-division-combine lib proofs)` | The Step assembling the conjunction of the given Steps in their order. |
| `(t4-division-times a b)` | The binary product term. |
| `(t4-division-one-product lib typed)` | The product identity for 1 and the integer named by the Step `typed`. |
| `(t4-division-zero-product lib typed)` | `(cons step lib)` for the product of the integer in `typed` and zero. |
| `(t4-division-product-difference lib d a b integers)` | The Step expressing the difference of scaled terms `a` and `b` as a scaled difference. |
| `(t4-division-product-order lib d a b integers positive-d order strict)` | `(cons step lib)` for the comparison scaled by `d`. |
| `(t4-division-derive-product-order lib d a b integers positive-d order strict)` | `(cons step lib)` for the derivation of the scaled comparison. |
| `(t4-division-cancel-product-order lib d a b ints positive-d strict)` | `(cons step lib)` for the strict comparison after removing the positive factor. Here `strict` is the Step for the scaled comparison. |
| `(t4-division-quotient-assumptions n divisor)` | The conjunction term of the integer quotient hypotheses. |
| `(t4-division-quotient-property n divisor value)` | The conjunction term bounding the natural quotient `value`. |
| `(t4-division-quotient-lemma lib)` | The Library with the integer quotient bound. |
| `(t4-division-positive-nonzero lib typed holds)` | The Step showing that the integer in `typed` is nonzero using the positivity Step `holds`. |
| `(t4-division-inverse-product lib typed-factor typed-value positive-factor)` | The Step canceling the reciprocal of a positive factor. The last three arguments are Steps. |
| `(t4-division-cross-multiply lib rational-identity typed positive-d positive-r)` | The Step clearing denominators in the rational identity Step. `typed` is the list of four integer Steps for the dividend, radix, numerator and denominator in order. The last two arguments are positivity Steps. |
| `(t4-division-floor-assumptions n radix)` | The conjunction term of the positive integer floor hypotheses. |
| `(t4-division-floor-property n value)` | The conjunction term bounding the floor `value`. |
| `(t4-division-floor-lemma-below qtype qnonnegative qbound lib integers d m n i-m extra positive-d)` | `(cons step lib)` for the conjunction of the floor properties. The first three arguments are Steps for the type, nonnegativity and product bound of the branch result. `i-m` proves the numerator integer, `extra` proves its strict upper bound, and `positive-d` proves positivity of `d`. |
| `(t4-division-floor-lemma lib)` | The Library with the positive integer floor bound and any auxiliary lemmas it needs. |
| `(t4-division-floor-bound lib n radix i-n i-r positive-n large-r)` | `(cons steps lib)`, with the integrality, nonnegativity and strict upper bound Steps in order. The last four arguments are Steps for integrality of `n` and `radix`, positivity of `n` and the comparison `1 < radix`. |

`integers` and `ints` are ordered lists of integer Steps. `positive-d`
and `order` are Steps for positivity and the unscaled comparison.
For `t4-division-product-order` and `t4-division-derive-product-order`,
`strict` is a Boolean selecting the strict comparison.

The three term constructors `t4-division-times`,
`t4-division-quotient-assumptions` and `t4-division-quotient-property`,
and the two floor term constructors do not return a failure. The other functions
may return a failure in place of the result. `conjunction` and `combine`
return a failure for an empty list.

`*t4-division-quotient*`, `*t4-division-floor*`,
`*t4-division-numerator*`, `*t4-division-denominator*`,
`*t4-division-reciprocal*`, `*t4-division-fix*`, `*t4-division-ifix*`,
`*t4-division-acl2-nfix*` and `*t4-division-numeric-equal*` are the
prover symbols used by these recipes.
