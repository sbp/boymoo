# Atom order

`library` is the Library in `prover/sig/library.md`. A `formula` is a prover
term in the form described in `prover/sig/proof.md`. `name` is the theorem
name string, as passed to `tactics.solve`.

| Call | Result |
|---|---|
| `(h3-atom-order-alphorder-reflexive library formula)` | `(cons step library)` with the proof of reflexivity and the Library containing the auxiliary lemmas in insertion order. A failure from proof construction is the entire result. |
| `(h3-atom-order-alphorder-law library name formula)` | `(cons step library)` with the proof of the given law and the Library containing the auxiliary lemmas in insertion order. A failure from proof construction is the entire result. |
