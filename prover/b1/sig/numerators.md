# Numerators of rationals

`lib` is a B1 Library. Formulas, terms and Steps follow
`prover/sig/proof.md`. Every call can return a failure in place of its
entire result. Where the Library may gain auxiliary lemmas, the
result is `(cons step lib)` with the resulting Library.

| ACL2 call | Result |
|---|---|
| `(b1-numerators-numerator-is-integer lib argument)` | A Step proving that the numerator of term `argument` is integer. |
| `(b1-numerators-equal-numerator lib formula)` | A Step for the equality term `formula` relating a numerator equality to integrality. |
| `(b1-numerators-unit-denominator lib formula)` | A Step for the translated implication term `formula` that a rational with denominator one equals its numerator. |
| `(b1-numerators-negative-numerator lib formula)` | A Step for the equality term `formula` expressing when a numerator is negative, with the resulting Library. |
| `(b1-numerators-numerator-negation lib argument)` | A Step equating the numerator of the negation of term `argument` to the negation of its numerator, with the resulting Library. |
| `(b1-numerators-numerator-distribute-sign lib formula)` | A Step for the equality term `formula` distributing the sign of a sum or product under the numerator, with the resulting Library. |
| `(b1-numerators-positive-reciprocal-numerator lib integral strict)` | A Step equating the numerator of a reciprocal to one, with the resulting Library. `integral` and `strict` prove that the argument of the reciprocal is a positive integer. |
| `(b1-numerators-reciprocal-numerator lib formula)` | A Step for the translated implication term `formula` expressing the numerator of a reciprocal as a sign, with the resulting Library. |
| `(b1-numerators-numerator-upper-bound lib formula)` | A Step for the translated implication term `formula` bounding the numerator of a quotient, with the resulting Library. |
