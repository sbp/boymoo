# Symbol tables

`lib` is a Library with the T3 proof rules for its dispatch tag. Terms, Steps
and entries use the forms in `prover/sig/proof.md` and `prover/sig/library.md`.
A failure is the entire result, including for calls that extend the Library.

| Call | Result | Failure |
|---|---|---|
| `(t3-book-symbol-tables-literal-table lib value)` | Pair `(cons step lib)` with the symbol-table recognition Step for quoted term `value` and the Library containing the constructor lemma. The proof visits the literal entries from last to first. | `unsupported` for a nonquoted or noncompound table, or a failure from constructing the proof. |
| `(t3-book-symbol-tables-symbol-keys lib)` | Library with the lemma that membership in a symbol table's keys implies symbolhood. | A failure from constructing or adding the lemma. |
| `(t3-book-symbol-tables-symbol-keys-inspect guard lib member)` | Equality Step exposing the key membership test under Step `guard`. | A failure from constructing the proof. |
| `(t3-book-symbol-tables-primitive-symbol lib name formula)` | Pair `(cons entry lib)` with the theorem entry for symbol `name` and implication `formula`, and the Library with the key and literal-table lemmas. | `unsupported` when the premise is no key lookup or its table is unsupported, or a failure from constructing the proof. |

The constants `*t3-book-symbol-tables-member*`, `*t3-book-symbol-tables-strip*`,
`*t3-book-symbol-tables-symbol-table*` and `*t3-book-symbol-tables-symbolp*`
are prover symbols. `*t3-book-symbol-tables-key-symbol*` is the unprefixed lemma name.
