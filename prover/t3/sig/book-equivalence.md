# Equality after canonicalization

`lib` is a Library with the T3 proof rules selected by its dispatch tag. A term
and a Step have the forms in `prover/sig/proof.md`. The functions leave the
Library unchanged.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t3-book-equivalence-parts formula)` | The tests along the true branches of IF terms whose false branch is quoted NIL, followed by the terminal term. | A failure from a malformed IF. |
| `(t3-book-equivalence-equality-boolean lib equality)` | A Step proving `BOOLEANP` of the equality term `equality`. | A failure from proof construction. |
| `(t3-book-equivalence-equality-relation lib formula)` | A Step proving the four equivalence properties in `formula`, or `nil` if the formula or unfolded relation has another shape. | A failure from reading a malformed term or constructing a Step. |
