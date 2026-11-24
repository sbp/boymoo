# Common divisors and Bézout coefficients

`lib` is a Library. Terms, Steps and binding maps use the shared forms.
The constants `*t2-euclid-gcd*`, `*t2-euclid-coeff-x*` and
`*t2-euclid-coeff-y*` are the three recursive function names.
`*t2-euclid-functions*` lists them in that order. `*t2-euclid-measure*`
is their common measure, and `*t2-euclid-first-coefficient*` and
`*t2-euclid-second-coefficient*` are the formal coefficient names.

All lists below retain the order of the source arguments or results. A
domain is a list of five Steps proving that the inputs are integers, that
each is nonnegative, and that at least one is positive, in that order.
A property group consists of seven terms or seven Steps in the order
returned by `t2-euclid-properties`. Every proof recipe can return a failure
in place of its entire result.

| Function | Arguments and result |
|---|---|
| `(t2-euclid-selection left right)` | The term testing whether either input term is positive, with the left test first. Cannot fail. |
| `(t2-euclid-either-positive lib left right evidence)` | The Step for the selection of `left` and `right` using the positivity Step `evidence`. |
| `(t2-euclid-descents lib)` | Library extended with the two subtraction descent lemmas. |
| `(t2-euclid-install lib)` | Library extended with the three recursive definitions and their measure proof. |
| `(t2-euclid-multiple divisor value)` | The term for the reciprocal of `divisor` times `value`. Cannot fail. |
| `(t2-euclid-properties x y)` | The terms for integrality and positivity of the divisor, integrality of each coefficient, reconstruction, and integrality of each quotient, in that order. Cannot fail. |
| `(t2-euclid-branch-values lib evidence)` | The three definition Steps selected using the list of evidence Steps. |
| `(t2-euclid-scale-difference lib scale whole part)` | The distributivity equality Step for `scale` times the difference of `whole` and `part`. |
| `(t2-euclid-restore-combination lib whole part a b)` | The equality Step from the difference-based combination to the combination of the original terms with coefficients `a` and `b - a`. |
| `(t2-euclid-reconstruction-lemmas lib)` | Library extended with the combination and divisibility reconstruction lemmas. |
| `(t2-euclid-combination lib whole part first second)` | The combination reconstruction Step at two input terms and two coefficient terms. |
| `(t2-euclid-restore-divisibility lib whole part divisor divides-difference divides-part integers)` | The divisibility Step for `whole`, from the Steps for the difference and the part, and the list of integer Steps. |
| `(t2-euclid-base lib domain x-positive)` | A conjunction Step for the property group in the base case selected by `x-positive`. |
| `(t2-euclid-descend lib formula domain subtract-from-x)` | The two-element list of the conjunction Step for the property group and the ordered substitution pairs for the indicated recursive branch. |
| `(t2-euclid-build lib)` | Library extended with the descents, definitions, reconstruction lemmas and invariant, in that order. |
| `(t2-euclid-invariant lib first second int-first int-second bound-first bound-second positive-arg)` | The seven property Steps for terms `first` and `second`, given the two integer Steps, the two nonnegativity Steps and a positivity Step for either term. |

The base-case call returns its conjunction Step paired with the resulting
Library as `(cons step lib)`. Constructing the divisibility and coefficient
proofs can add the product-zero lemma to that Library.
