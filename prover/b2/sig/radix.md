# Radix

Terms, symbols, and Steps have the forms specified in `prover/sig/proof.md`.
Libraries have the form specified in `prover/sig/library.md`. Both functions
return `(cons step lib)` with the resulting Library. A failure is the entire
result.

`*b2-radix-digit*` and `*b2-radix-zp*` are prover symbols.

| Function | Arguments in order | Result | Failure |
|---|---|---|---|
| `b2-radix-digit-character` | Library, digit conversion call term | Pair with the Step proving that the call returns a character | May return a failure |
| `b2-radix-character-accumulator` | Library, induction formula | Pair with the Step proving the accumulator preserves character lists | May return a failure |
