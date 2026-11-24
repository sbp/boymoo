# Projections

Terms, symbols, and Steps have the forms specified in `prover/sig/proof.md`.
Libraries have the form specified in `prover/sig/library.md`. Both functions
return `(cons step lib)` with the resulting Library. A failure is the entire
result.

`*b2-projections-mv-nth*` and `*b2-projections-zp*` are prover symbols.

| Function | Arguments in order | Result | Failure |
|---|---|---|---|
| `b2-projections-mv-nth` | Library, integer index, projected term | Pair with the Step equating the projection to its selector term | May return a failure, including `Fuel` |
| `b2-projections-projected-value` | Library, integer index, equation Step, evidence Step list | Pair with the Step projecting and normalizing the equation's result | May return a failure |
