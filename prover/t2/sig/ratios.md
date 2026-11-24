# Reduced rational components

A Library and a Step have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. A term is a prover term. An argument described as a
proof is a Step. Lists of results use the field order shown below. The constant `*t2-ratios-abs*` is the symbol for `ABS`.

| Function | Arguments in order | Result |
| --- | --- | --- |
| `t2-ratios-numerator` | Term | Application of `NUMERATOR` to the term |
| `t2-ratios-denominator` | Term | Application of `DENOMINATOR` to the term |
| `t2-ratios-cancel-positive` | Library, positivity proof for the factor, integrality proof for the factor, integrality proof for the value | Equality Step for multiplication by the factor and its inverse |
| `t2-ratios-reduced-pair` | Library, rationality proof, Boolean for a negative numerator | List of the linear-combination equality and the two coefficient integrality Steps |
| `t2-ratios-multiply-representation` | Library, coefficient term, inverse denominator term, component term, multiplier term, simplifying equality Step | Equality Step for the rearranged product |
| `t2-ratios-denominator-divides` | Library | Library with `DENOMINATOR-DIVIDES` |
| `t2-ratios-multiplier-ratio` | Library, rationality proof for the value, integrality and positivity proofs for the multiplier, integrality proof for the product | List of the quotient's integrality and positivity Steps |
| `t2-ratios-at-least-one` | Library, positivity proof, integrality proof | Weak lower-bound Step |
| `t2-ratios-denominator-bound` | Library | Library with `DENOMINATOR-BOUND` |
| `t2-ratios-same-denominator` | Library, left and right rationality proofs, integrality proof for the left value times the right denominator, integrality proof for the right value times the left denominator | Equality Step for the denominators |
| `t2-ratios-multiplied-negative` | Library, rationality proof | Integrality Step for the negated value times the denominator |
| `t2-ratios-symmetry` | Library | Library with the negation lemmas |
| `t2-ratios-translate` | Library | Library with the integer translation lemmas |
| `t2-ratios-integer-quotient` | Library | Library with `DENOMINATOR-INTEGER-QUOTIENT` |
| `t2-ratios-absolute` | Library, proof for the sign of the argument | Equality Step for the applicable branch of absolute value |
| `t2-ratios-absolute-integers` | Library | Library with the integrality and nonnegativity lemmas for absolute value |
| `t2-ratios-absolute-growth` | Library | Library with the growth lemmas for absolute value |
| `t2-ratios-numerator-after-division` | Library | Library with `NUMERATOR-DIVIDED-BOUND` |
| `t2-ratios-reciprocal-components` | Library | Library with `RATIONAL-RECIPROCAL-COMPONENTS` |
| `t2-ratios-unit-numerator` | Library | Library with the unit-numerator lemmas |
| `t2-ratios-build` | Library | Library extended with the Euclidean and reduced-component lemmas, in that order |

The two term constructors cannot fail. All other functions can return
a failure in place of the listed result. Library entries retain their
insertion order.
