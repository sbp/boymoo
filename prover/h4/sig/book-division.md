# Bounds on nonnegative quotients

The symbol constants have the prefix `*h4-book-division-` and the
following names, followed by `*`.
`quotient`, `quotient-bounds`, `floor`, `numerator`, `denominator`,
`floor-bounds`, `fix`, `ifix`, `acl2-nfix` and `reciprocal`.

The first argument `p` is a Library. `integers` is an ordered list
of integer evidence Steps. Terms and Steps use the shared forms.
Except for `times`, each function may return a failure.

| Call | Result |
|---|---|
| `(h4-book-division-conjunction p proofs)` | The conjunction Step from the nonempty list of evidence Steps, associated from the right. An empty list produces a failure. |
| `(h4-book-division-times a b)` | The product term of `a` and `b` in that order. |
| `(h4-book-division-left-product-one p factor integers)` | A Step equating the product of one and the factor to the factor. |
| `(h4-book-division-product-one p factor integers)` | A Step equating the product of the factor and one to the factor. |
| `(h4-book-division-product-zero p factor integers)` | A Step equating the product of the factor and zero to zero. |
| `(h4-book-division-product-negative p factor value integers)` | A Step moving the negation of the second factor outside the product. |
| `(h4-book-division-nonzero p strict)` | A Step showing the positive term in the strict comparison Step is nonzero. |
| `(h4-book-division-shift-weak-bound p bound offset integers)` | The weak comparison Step with the offset added on the left of each side. |
| `(h4-book-division-quotient-bounds p)` | `(cons name library)` for the quotient bounds lemma and the Library with that lemma added. |
| `(h4-book-division-positive-product p first second integers)` | The Step proving positivity of the product from Steps for positivity of its factors in order. |
| `(h4-book-division-cancel-positive-factor p comparison left right positive-factor integers)` | The Step for the strict comparison of the two terms from a comparison Step scaled by the same positive factor. |
| `(h4-book-division-cancel-reciprocal p factor value positive-factor integers)` | A Step cancelling the positive factor term and its reciprocal when multiplying the value term. |
| `(h4-book-division-multiply-equality p factor equality)` | A Step applying multiplication on the left by the factor term to the two sides of the equality Step. |
| `(h4-book-division-ratio-scaling p value divisor ratio numerator denominator ratio-type divisor-positive denominator-positive integers)` | A Step equating the divisor times the numerator to the denominator times the value. The first five arguments after the Library are terms and the next three are Steps. |
| `(h4-book-division-floor-bounds p)` | `(cons name library)` for the floor bounds lemma and the Library with that lemma added. |
