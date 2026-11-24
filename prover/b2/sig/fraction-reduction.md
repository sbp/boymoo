# Fraction reduction

Terms, symbols, and Steps have the forms specified in `prover/sig/proof.md`.
The first argument of a proof recipe is a Library as specified in
`prover/sig/library.md`. An evidence argument is an ordered Step list.
A result described as a pair is `(cons value lib)` with the resulting
Library. A failure is the entire result.

`*b2-fraction-reduction-common*` is the symbol of the common denominator
function.

| Function | Arguments in order | Result | Failure |
|---|---|---|---|
| `b2-fraction-reduction-triple` | Three terms | The term constructing their three-element list | — |
| `b2-fraction-reduction-sum-unit` | Library, term, numeric Step | Step for the additive unit | May return a failure |
| `b2-fraction-reduction-negative-factor` | Library, left factor term, right factor term | Pair with the Step moving a minus from the right factor outside the product | May return a failure |
| `b2-fraction-reduction-negative-first` | Library, left factor term, right factor term | Pair with the Step moving a minus from the left factor outside the product | May return a failure |
| `b2-fraction-reduction-twice-negated` | Library, term, numeric Step or `nil` | Step cancelling double negation | May return a failure |
| `b2-fraction-reduction-positive-denominators` | Left and right denominator terms | Conjunction of positivity and integrality conditions | — |
| `b2-fraction-reduction-common-conditions` | Value term, left denominator term, right denominator term | Premise for the common denominator representation | — |
| `b2-fraction-reduction-common-properties` | Value term, left denominator term, right denominator term, common divisor term, left factor term, right factor term | Conclusion for the common denominator representation | — |
| `b2-fraction-reduction-projected-properties` | Value term, left denominator term, right denominator term, result term | Conclusion with fields projected from the result term | — |
| `b2-fraction-reduction-difference-bounds` | Library, larger term, smaller term, positivity Steps for the larger and smaller terms, comparison Step, integer evidence | Two Steps for positivity of the difference and its strict decrease in count, in that order | May return a failure |
| `b2-fraction-reduction-install-common` | Library | Library extended with a common denominator definition and its measure | May return a failure |
| `b2-fraction-reduction-integer-product-difference` | Library, value term, larger term, smaller term, evidence | Pair with the Step proving the product with the difference is integral | May return a failure |
| `b2-fraction-reduction-common-lemma` | Library | Pair with the name of the common representation lemma | May return a failure |
| `b2-fraction-reduction-reduces-to-unit` | Library, value term, rationality Step, representation Step, denominator equation Step, factor term, unit term, evidence | Step proving the factor equals one | May return a failure |
| `b2-fraction-reduction-negated-fraction` | Library, value term, rationality Step, Boolean selecting the denominator | Pair with the Step proving the selected numerator or denominator equation | May return a failure |
| `b2-fraction-reduction-fraction-minus` | Library, theorem name symbol, theorem formula | Pair with the Step proving the formula | May return a failure |
