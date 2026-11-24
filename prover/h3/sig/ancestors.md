# Ancestor membership

`library` is the Library in `prover/sig/library.md`. A `formula` is a prover
term in the form described in `prover/sig/proof.md`.

| Call | Result |
|---|---|
| `(h3-ancestors-ancestors-check library formula)` | `(cons step library)` with the proof of `formula` and the Library containing the auxiliary lemmas in insertion order. A failure from proof construction is the entire result. |
