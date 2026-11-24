# Rounding relations

The Library, terms and Steps have the forms in `prover/sig/library.md`
and `prover/sig/proof.md`.

| Call | Result | Failure |
|---|---|---|
| `(b2-rounding-relations-floor-as-truncate library formula)` | `(cons step library)` with the Step proving the theorem term `formula` and the resulting Library. | May return a failure during proof construction. |

`*b2-rounding-relations-floor-as-truncate*` is the theorem symbol
`FLOOR-AS-TRUNCATE`.
