# Nonnegative integer quotient

The constants are `*t2-quotient-quotient*` and `*t2-quotient-quotient-fact*`.
`lib` is the Arithmetic library. Terms and Steps use the forms in
`prover/sig/proof.md`. `i` is a dividend term and `j` is a divisor term.
`ij` and `integers` are lists of integer evidence Steps in argument order.
A result of `(cons value lib)` includes the Library's resulting entries and
facts in insertion order.

| Call | Result | Failure |
|---|---|---|
| `(t2-quotient-quotient-domain i j)` | The conjunction of the dividend and divisor conditions. | None. |
| `(t2-quotient-quotient-properties i j)` | The conjunction of the naturalness of the quotient and the upper product bound. | None. |
| `(t2-quotient-quotient-equation lib i j ij pos-j)` | A Step opening the quotient. `pos-j` proves the divisor positive. | May fail. |
| `(t2-quotient-prove-quotient-bound lib)` | Library with the general bound lemma. | May fail. |
| `(t2-quotient-quotient-bound lib i j integers nonnegative-i positive-j)` | `(cons (list natural bound) lib)`. The last two arguments prove nonnegativity of `i` and positivity of `j`. | May fail. |
| `(t2-quotient-build-quotient-descent lib)` | Library with the count decrease lemma for a positive integer dividend and an integer divisor greater than one. An auxiliary induction proves naturalness and additive bounds on the quotient. | May fail. |
