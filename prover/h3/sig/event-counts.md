# Event counts

`library` is the Library in `prover/sig/library.md`. A `factor` or `formula`
is a prover term in the form described in `prover/sig/proof.md`.

| Call | Result |
|---|---|
| `(h3-event-counts-multiply-zero library factor)` | Step proving `factor * 0 = 0`. A failure from proof construction is the entire result. |
| `(h3-event-counts-event-count library formula)` | `(cons step library)` with the proof of the type or cutoff formula and the Library containing the auxiliary lemmas in insertion order. A failure from proof construction is the entire result. |
