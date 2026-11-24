# Numeric type tests

Terms, Steps and the Library use the forms in `prover/sig/proof.md` and
`prover/sig/library.md`. Every non-lifted call below takes a Library first and can return
a failure from proof construction.

| Call | Arguments and result |
|---|---|
| `(t2-numeric-types-one-bound lib strictly-positive integral)` | The weak lower-bound Step at one for the term whose positive and integer Steps are supplied. |
| `(t2-numeric-types-build lib)` | Library with the numeric type lemmas in recipe order. |
| `(t2-numeric-types-type-under-involution lib operation label predicate bool-axiom closure)` | Library with the type-preservation lemma. `operation` is `:minus` or `:reciprocal`, `label` names the involution lemma, `predicate` is its type-test symbol, and `bool-axiom` names the Boolean fact. The closure function is represented by `:rational` for the rational recipe or `:integer` for the Library's integer recipe. |
| `(t2-numeric-types-build-rational-type term evidence lib)` | Rational Step for the term from the list of evidence Steps. |
| `(t2-numeric-types-fixed-order lib)` | Library with the order invariance lemma for numeric fixing. |
| `(t2-numeric-types-reciprocal-negation lib)` | Library with the reciprocal of a negation lemma. |
| `(t2-numeric-types-reciprocal-above-one lib)` | Library with the noninteger reciprocal lemma for arguments above one. |
| `(t2-numeric-types-reflected-order lib value constant-value)` | The order-reflection Step with the negated constant evaluated. `value` and `constant-value` are terms. |
| `(t2-numeric-types-reciprocal-below-minus-one lib)` | Library with the noninteger reciprocal lemma for arguments below minus one. |
| `(t2-numeric-types-positive-integer-above-one lib integral sign different)` | Strict lower-bound Step at one from integral, positive and distinct-from-one Steps. |
| `(t2-numeric-types-integral-reciprocal lib)` | Library with the integrality test for reciprocals of integers. |

The lifted `build-rational-type` function takes its captured `lib`
after `term` and `evidence`, as shown in the table.
