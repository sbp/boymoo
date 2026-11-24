# Index and output column phases

`lib` is a Library. `evidence` is an Evidence object from `logic.lisp`.
Terms and Steps have the forms in `prover/sig/proof.md`.
`*t3-formatting-fmt-tilde*` and `*t3-formatting-margin*` are the ACL2
symbols for the formatter and its right margin. `*t3-formatting-fmt-predicates*`
is the ordered list of predicates for establishing formatting bounds.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t3-formatting-formatting-measure index end column)` | An ordinal term for index term `index`, endpoint term `end`, and column term `column`. | None. |
| `(t3-formatting-nonzero-column lib phase evidence)` | `(cons step evidence)` with a proof that the column in phase term `phase` is nonzero and the updated Evidence. The right-margin test is the first matching fact in insertion order. | `Unsupported` for a missing right-margin test, or a failure from evidence or proof construction. |
| `(t3-formatting-formatting-descent lib smaller larger evidence)` | `(step lib evidence)` with a proof of descent between the two ordinal terms and the resulting Library and Evidence. | A failure from evidence or proof construction. |
