# Integer power result types

`lib` is a B2 tactics library. Terms and Steps follow `prover/sig/proof.md`.

The theorem symbols are `*b2-exponent-types-positive*`,
`*b2-exponent-types-nonzero*`, `*b2-exponent-types-integer*` and
`*b2-exponent-types-unit*`. `*b2-exponent-types-exponent-types*` is the
membership list of those symbols in that order.

| Call | Result | Failure |
|---|---|---|
| `(b2-exponent-types-excluded-zero lib premise)` | `(cons step lib)` with the nonzero result obtained from reciprocal identity Step `premise` and the resulting library. | Failure from unpacking the premise or constructing the proof. |
| `(b2-exponent-types-exponent-type lib name formula)` | `(cons step lib)` with the proof of term `formula` for theorem symbol `name` and the resulting library. | Unknown theorem name or failure in unfolding or proving the formula. |
