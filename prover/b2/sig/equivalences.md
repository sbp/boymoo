# Equivalences

`lib` is a Library as described in `prover/sig/library.md`. Terms, symbols, and Steps are described in `prover/sig/proof.md`. Each call can return a failure in place of the result.

| Call | Result |
|---|---|
| `(b2-equivalences-equiv-call lib call)` | Boolean indicating whether `call` is a binary application of a defined equivalence relation. |
| `(b2-equivalences-opened-equivalence lib call)` | Equation Step obtained by normalizing the equivalence application `call` to an equality of fixed values. Returns `unproved` when the relation or characterization is absent. |
| `(b2-equivalences-equality-of-fixed lib step)` | Step for the equality of fixed values, given a Step establishing an equivalence or an equality. |
| `(b2-equivalences-equivalence-properties lib formula)` | Step for the equivalence properties in the translated proposition `formula`. Returns `unproved` when the expected form is absent. |
| `(b2-equivalences-congruence lib formula)` | Step for the congruence implication `formula`, or `unproved` when it cannot be established. |
| `(b2-equivalences-prove-equivalence lib formula)` | Step for the congruence implication, equivalence call, or equivalence properties in `formula`, or `unproved` when it cannot be established. |

`*b2-equivalences-booleanp*` is the `BOOLEANP` symbol. `*b2-equivalences-equivalence-suffixes*` is the ordered list of the suffixes used to recognize the relation names.
