# Lexicographic comparisons

`lib` is a Library and `formula` is the equality term for the comparison theorem. A Step follows `prover/sig/proof.md`. Each call can return a failure from reading a term or constructing a proof.

| Call | Result |
|---|---|
| `(b1-lexical-fast-lexorder lib formula)` | Step for the equality of `FAST-LEXORDER` and `LEXORDER`. |
| `(b1-lexical-fast-strict-order lib formula)` | `(cons step lib)` with the Step for the equality of `FAST-<<` and `<<` and the Library carrying its auxiliary lemmas in insertion order. |
