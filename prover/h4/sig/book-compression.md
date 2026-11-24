# Ordinal compression

`p` is the H4 Tactics library. Terms and Steps use the forms in
`prover/sig/proof.md`. Lists of Steps preserve the supplied order. A failure
replaces the entire result.

The constants `*h4-book-compression-e0-ordinal*`,
`*h4-book-compression-atoc*`, `*h4-book-compression-add*`, and
`*h4-book-compression-fix*` are the prover symbols `E0-ORDINALP`,
`ATOC`, `OB+`, and `FIX` in the ACL2 package.

| Call | Result | Failure |
|---|---|---|
| `(h4-book-compression-cons-evidence p value)` | The three Steps for `CONSP`, `CAR`, and `CDR` of the term `value`, using the arguments of `value` in order. | A failure from proof construction. |
| `(h4-book-compression-nonzero-cons p shape)` | A Step that the term in the `CONSP` Step `shape` is distinct from quoted zero. | A failure from proof construction. |
| `(h4-book-compression-ordinal-cells p exponent coefficient tail)` | `(raw shapes projections)` for the cons representation of the ordinal with the three given terms. `shapes` contains the two `CONSP` Steps for the outer and inner cons, in that order. `projections` gives the `CAR`, `O-FIRST-EXPT`, `O-FIRST-COEFF`, and `O-RST` equality Steps in that order. | A failure from proof construction. |
| `(h4-book-compression-typed-ordinal-cells p exponent coefficient tail facts)` | The `O-P` and `CONSP` Steps for the `MAKE-ORD` term in that order, using the evidence Steps `facts`. | A failure from proof construction. |
| `(h4-book-compression-zero-plus-ordinal p typ shape)` | A Step that adding zero to the ordinal in the `O-P` Step `typ` gives that ordinal, using its cons or atom Step `shape`. | A failure from proof construction. |
| `(h4-book-compression-coefficient-successor p positive)` | A `POSP` Step for one plus the coefficient in the `POSP` Step `positive`. | A failure from proof construction. |
| `(h4-book-compression-singleton-sum-init p exponent tail-type)` | A SingletonSum for the term `exponent` and the right summand in the `O-P` Step `tail-type`. | A failure from proof construction. |
| `(h4-book-compression-singleton-sum-reduce single p shape facts)` | A Step reducing the addition in `single`, using the right summand's cons or atom Step `shape` and the evidence Steps `facts`. | A failure from proof construction. |
| `(h4-book-compression-singleton-sum-finite-bounds single p exponent-type nonzero shape)` | `(signs strict)`, where `signs` is the list of Steps for zero strictly below the exponent and the exponent not strictly below zero, in that order. `strict` proves that the first exponent of the right summand is strictly below the exponent in `single`. The inputs are an `O-P` Step and a nonzero Step for the exponent and an atom Step for the right summand. | A failure from proof construction. |
| `(h4-book-compression-singleton-ordinal-sum p)` | A Step that adding a single term of nonzero ordinal exponent to an ordinal gives a nonfinite ordinal. | A failure from proof construction. |
| `(h4-book-compression-compression-shape formula)` | The subject of an implication from `E0-ORDINALP` of an atomic term to `O-P` of its `ATOC`, or `nil` when the formula does not match. | A failure from reading a malformed formula. |
| `(h4-book-compression-compression-proof p formula support)` | A Step for the matching `formula` using the given support facts, or `nil` when the formula does not match or `support` is empty. `support` is an insertion-ordered alist of fact names and clauses. | A failure from matching or proof construction. |
| `(h4-book-compression-compress-ordinal p formula subject)` | A Step for the compression implication `formula` about `subject`, with the needed support facts in `p`. | A failure from proof construction. |

A SingletonSum has the form
`(:h4-book-compression-singleton-sum exponent tail-type result tail-exponent raw shapes projections start)`.
Its fields are the exponent term, the right summand's `O-P` Step, the
addition term, the first-exponent term of the right summand, the raw
single-term ordinal cons, its shape Steps, its projection Steps, and the
Step exposing the raw sum. The accessors take the SingletonSum and
return their respective fields.

- `h4-book-compression-singleton-sum-exponent`
- `h4-book-compression-singleton-sum-tail-type`
- `h4-book-compression-singleton-sum-result`
- `h4-book-compression-singleton-sum-tail-exponent`
- `h4-book-compression-singleton-sum-raw`
- `h4-book-compression-singleton-sum-shapes`
- `h4-book-compression-singleton-sum-projections`
- `h4-book-compression-singleton-sum-start`
