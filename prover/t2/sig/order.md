# Rational order and scaling

In each call, `lib` is the Library containing the arithmetic definitions and
facts. Terms, Steps, and Library objects use the representations in
`prover/sig/proof.md` and `prover/sig/library.md`. A strict comparison Step has
`(< a b)` as its first literal. The lists `known`, `rats`, and `types` contain
rationality Steps in the order in which the caller supplies them. A lookup
in `known` returns the first Step with a matching first literal.

Every call can return `(:failure kind message)` from its proof operations.
A failure is the entire result. A Step result leaves `lib` unchanged unless
the result column includes the Library.

| ACL2 call | Arguments and result |
|---|---|
| `(t2-order-rational lib term known)` | Rationality Step for `term`, using `known` and closure of rational arithmetic. |
| `(t2-order-number-from-rational lib evidence)` | Number Step for the term in the rationality Step `evidence`. |
| `(t2-order-negate-difference lib a b)` | Step equating the negation of `a - b` to `b - a`. The inputs are terms. |
| `(t2-order-trichotomy lib a b rats)` | Step proving `b < a` under the hypotheses that terms `a` and `b` differ and `a < b` is false, using the rationality Steps `rats`. |
| `(t2-order-irreflexive lib value)` | Step denying `value < value` for term `value`. |
| `(t2-order-strict-chain lib first second)` | Pair `(cons step lib)` for the composition of the strict comparison Steps `first` and `second`. The returned Library includes `FIELD-LESS-TRANSITIVE`, added once if absent. An unequal middle endpoint returns a failure. |
| `(t2-order-opposite-order lib strict)` | Step denying the reversed comparison of the strict comparison Step `strict`. |
| `(t2-order-increasing-product lib comparison factor-positive types)` | Step scaling the strict comparison Step `comparison` on the left by the factor shown positive by `factor-positive`, using rationality Steps `types`. |
| `(t2-order-boolean-less lib formula)` | Boolean Step for comparison term `formula`. |
| `(t2-order-positive-scaling lib)` | Library with `FIELD-POSITIVE-SCALE` and any auxiliary lemmas used in its proof. |
| `(t2-order-zero-from-sign lib value nonpos nonneg numeric)` | Step equating term `value` to zero using the nonpositivity, nonnegativity, and number Steps `nonpos`, `nonneg`, and `numeric`. |
| `(t2-order-negate-left-factor lib a b)` | Step equating the product of `-a` and `b` to the negation of the product of `a` and `b`. The inputs are terms. |
| `(t2-order-complete-scaling lib)` | Library with negative, complete, and unit scaling lemmas, in insertion order. |
| `(t2-order-distinct lib strict)` | Step denying equality of the two operands of the strict comparison Step `strict`. |
| `(t2-order-scaled-quotient lib numerator divisor denominator-type distinct-from-zero types)` | Step equating the left product of term `divisor` and the quotient to term `numerator`. `denominator-type` and `distinct-from-zero` establish rationality and nonzeroness of `divisor`. `types` supplies the other rationality Steps. |
| `(t2-order-normalizing-quotients lib)` | Library with comparison normalization lemmas for reciprocals and quotients, in insertion order. |
| `(t2-order-reciprocal-signs lib)` | Library with the positive and negative sign lemmas for reciprocals, in that order. |
| `(t2-order-numerator-signs lib)` | Library with the positive and negative sign lemmas for numerators, in that order. |
| `(t2-order-product-signs lib)` | Library with the negative and positive sign lemmas for products, in that order. |
| `(t2-order-build lib)` | Library extended with the scaling, normalizing, and sign lemmas, in the order in which the recipes add them. |

The functions returning a Library alone install the corresponding lemmas.
