# Division

`lib` is a B1 Library. Terms and Steps have the forms in `prover/sig/proof.md`.
Evidence is a list of Steps in the order supplied. Each function can return a failure
in place of the whole result. When a result includes an updated Library, it is
`(cons value lib)`. A missing Step is `nil`.

| ACL2 call | Result |
|---|---|
| `(b1-division-bool-less lib formula)` | A Step proving the comparison term `formula` is Boolean. |
| `(b1-division-positive-scale lib comparison strict rational evidence)` | An equality Step relating the comparison term to its scaled form, paired with the updated Library. `strict` and `rational` are positivity and rationality Steps for the scale factor. |
| `(b1-division-extract-factor lib term factor)` | An equality Step grouping the term `factor` at the left of the product term `term`, or `nil` when it is absent. |
| `(b1-division-cancel-reciprocal lib factor argument inverse evidence)` | An equality Step cancelling the reciprocal of term `factor` in term `argument`, or `nil` when it is absent. `inverse` is the Step stating their product is one. |
| `(b1-division-scaled-compare lib before factor strict rational evidence reversed-order)` | A Step equating comparison term `before` with the comparison scaled by term `factor`, paired with the updated Library. `strict` proves positivity of the scale factor or its negation. `rational` proves rationality of the scale factor. Pass `nil` for the unreversed comparison. |
| `(b1-division-zero-product-rule lib term)` | An equality Step reducing a product term with a syntactic zero factor, or `nil`. |
| `(b1-division-product-with-inverse lib formula)` | A Step for the displayed inverse-product formula. |
| `(b1-division-divide-positive lib formula)` | A Step for the displayed positive-factor comparison formula, paired with the updated Library. |
| `(b1-division-align-comparison lib equivalence right)` | The equality Step `equivalence` with the products in its right side oriented to match term `right`. |
| `(b1-division-divide-by-sign lib formula inverted)` | A Step for the displayed comparison by sign, paired with the updated Library. Pass `nil` for the comparison in its given direction. |
| `(b1-division-scaled-equality lib comparison factor-type nonzero left-type right-type)` | A Step equating the equality test `comparison` with the test scaled by the factor. The remaining arguments are Steps proving its numeric type and nonzero value, and the two sides' numeric types. |
| `(b1-division-equal-tests lib original forward backward)` | A Step proving Boolean equality of the two tests using the three Steps for the original test and the two implications. |
| `(b1-division-zero-reciprocal lib term fixed-zero)` | A Step equating the reciprocal of `term` to zero given the equality Step `fixed-zero`. |
| `(b1-division-mixed-numeric-equality lib comparison nonnumeric numeric)` | A Step equating the equality test `comparison` to false using the two type Steps. |
| `(b1-division-multiply-division-equality lib formula)` | A Step for the displayed equality of an argument and a product by a reciprocal. |
| `(b1-division-reciprocal-equality lib formula)` | A Step for the displayed equality with a reciprocal. |
