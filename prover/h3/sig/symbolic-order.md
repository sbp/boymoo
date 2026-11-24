# String and symbol comparisons

The Library, term and Step arguments have the forms in the shared signatures.
Each call returns a Step, a list of Steps where specified, or a failure.
Evidence and type arguments are lists of Steps in the supplied order. A head
is the symbol term for the comparison function. Arguments `a`, `b` and
`c` are the terms being compared.

| Call | Result |
|---|---|
| `(h3-symbolic-order-guarded lib fact evidence)` | Consequent of the implication Step `fact`, after proving its guard using the evidence. |
| `(h3-symbolic-order-char-lists lib terms)` | Character-list recognition Steps for the ordered list of terms. |
| `(h3-symbolic-order-unsigned-list-comparison lib step)` | The comparison Step with the string comparison opened to its list form. |
| `(h3-symbolic-order-string-asymmetric lib forward)` | Denial of the reverse string comparison given the forward strict comparison Step. |
| `(h3-symbolic-order-asymmetry lib forward)` | Denial of the reverse string or symbol comparison given the forward strict comparison Step. |
| `(h3-symbolic-order-string-trichotomy lib a b not-forward)` | String-list trichotomy Step given the negated comparison Step. |
| `(h3-symbolic-order-coerce-injectivity lib a b types equal-lists)` | Equality Step given the two string type Steps and the equality Step for their list forms. |
| `(h3-symbolic-order-iff-left lib fact right-proof)` | Proof of the left side of the equivalence Step `fact` using the Step for its right side. |
| `(h3-symbolic-order-iff-deny-right lib fact denial)` | Denial of the right side of the equivalence Step `fact` using the Step denying its left side. |
| `(h3-symbolic-order-antisymmetry lib head a b types a-le-b b-le-a)` | Equality Step from the two weak comparison Steps and the type Steps. |
| `(h3-symbolic-order-strict-transitive lib head a b c types first second)` | Composition of the two strict comparison Steps using the type Steps. |
| `(h3-symbolic-order-transitivity lib head a b c types left right)` | Composition of the two weak comparison Steps using the type Steps. |
| `(h3-symbolic-order-boolean-string-order lib types length-name)` | Normalization Step for the Boolean value of `STRING<=`, using the type Steps and the symbol term naming the length lemma. |
| `(h3-symbolic-order-boolean-string-order-prove steps lib rules wanted)` | Step for term `wanted` using a Rules object and the ordered list of Steps. |

The symbol constants are `*h3-symbolic-order-string-lt*`,
`*h3-symbolic-order-string-le*`, `*h3-symbolic-order-coerce*`,
`*h3-symbolic-order-symbol-lt*` and `*h3-symbolic-order-iff*`.
The constant `*h3-symbolic-order-list*` is the quotation of `LIST`.
