# Products

`*b2-products-fix*`, `*b2-products-recip*`, `*b2-products-num*` and
`*b2-products-den*` are prover symbols. The library has the form in
`prover/sig/library.md`. Formulas, terms, and Steps have the forms in
`prover/sig/proof.md`. Evidence is a list of Steps in argument order.

Except for `b2-products-product`, every function below can return a failure
in place of its result. A result written `(cons step lib)` carries the
resulting Library, including any auxiliary lemmas, in its cdr. Other
functions leave the Library unchanged.

| Function | Arguments and result |
|---|---|
| `(b2-products-product a b)` | Terms in operand order. Returns their product term. |
| `(b2-products-numeric-closure lib term)` | Library and arithmetic term. Returns the closure Step for its operator. |
| `(b2-products-multiplicative-unit lib term numeric)` | Library, term, and its numeric Step. Returns the equality of its product with left operand one to the term. |
| `(b2-products-zero-product lib value)` | Library and term. Returns `(cons step lib)` for the product with right operand zero. |
| `(b2-products-product-completion lib a b evidence)` | Library, product operands, and evidence. Returns the product completion Step. |
| `(b2-products-reciprocal-identity lib value numeric nonzero)` | Library, term, and its numeric and nonzero Steps. Returns the inverse identity Step. |
| `(b2-products-distribute-cancel lib a b c unit numeric-c)` | Library, operand terms, Step for `a * b = 1`, and numeric Step for `c`. Returns the Step for `a * (b * c) = c`. |
| `(b2-products-product-swap lib a b c)` | Library and operand terms. Returns the Step for `a * (b * c) = b * (a * c)`. |
| `(b2-products-zero-left-product lib value)` | Library and term. Returns `(cons step lib)` for the product with left operand zero. |
| `(b2-products-inverse-from-product lib equality numeric-a nonzero-a)` | Library, Step for `a * b = 1`, and numeric and nonzero Steps for `a`. Returns the Step for `b = 1/a`. |
| `(b2-products-unique-inverse lib formula)` | Library and inverse uniqueness formula. Returns `(cons step lib)`. |
| `(b2-products-rational-factors lib value rational)` | Library, term, and its rationality Step. Returns the three Steps proving denominator integrality, numerator integrality, and denominator positivity, in that order. |
| `(b2-products-rational-product lib value rational)` | Library, term, and its rationality Step. Returns `(cons step lib)` for the product of the term and its denominator. |
| `(b2-products-integer-denominator lib value typed)` | Library, term, and its integer Step. Returns `(cons step lib)` for its denominator being one. |
| `(b2-products-completion-branch lib name value evidence)` | Library, axiom name string, term and evidence. Returns the completion Step on this branch. |
| `(b2-products-numerator-denominator lib name formula)` | Library, theorem symbol, and formula. Returns `(cons step lib)` for the named numerator or denominator property. |
| `(b2-products-floor-reassociate lib formula)` | Library and floor reassociation formula. Returns `(cons step lib)`. |
| `(b2-products-numerator-denominator-consequent typed lib name value)` | Integer Step, Library, theorem's unqualified name string, and term. Returns `(cons step lib)` for the implication's consequent. |
| `(b2-products-floor-reassociate-consequent evidence lib x z reciprocal-x reciprocal-z divisor candidate quotient zero operation opposite)` | Antecedent Step, Library, operand terms `x` and `z`, their reciprocal terms, divisor and candidate terms, quotient equality term, zero test term, and the two floor calls. Returns `(cons step lib)` for the implication's consequent. |

The consequent of floor reassociation takes the other numerator factor
from the second operand of the product in `operation`.
