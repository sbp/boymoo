# Recognizers of association list lookups

`lib` is a Library with the T3 proof rules for its dispatch tag. Terms and Steps
have the forms in `prover/sig/proof.md`. The constants are
`*t3-book-associations-assoc*`, `*t3-book-associations-by-cdr*`,
`*t3-book-associations-strip-cdrs*`, `*t3-book-associations-natp*`,
`*t3-book-associations-nat-table*`, `*t3-book-associations-fixnat-table*`,
`*t3-book-associations-symbol-table*`, `*t3-book-associations-term-list*`,
`*t3-book-associations-termp*` and `*t3-book-associations-symbolp*`.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t3-book-associations-components lib recognizer)` | Steps extracted from Step `recognizer`. Each true conjunction head comes before its rest. | A failure from reading or separating a Step, or `fuel` on exhaustion. |
| `(t3-book-associations-invariant lib label lookup table result)` | The updated Library with lemma name string `label` for lookup function symbol `lookup`, table recognizer term `table` and result template term `result`. | `unsupported` when the head's property is unavailable, `missing-proof-input` when the tail's property is unavailable, or a failure from proof construction. |
| `(t3-book-associations-associate lib name formula table)` | `(cons entry lib)` with the theorem entry for symbol `name` and formula term `formula`, and the Library with the auxiliary lookup lemma. `table` is the name of the recognizer. | A failure from the invariant, proof construction or serialization. |
