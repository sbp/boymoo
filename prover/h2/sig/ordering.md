# Ordering on character lists, strings, and symbols

`proof` is the H2 proof search object. Terms and Steps have the forms in
`prover/sig/proof.md`. The constants `*h2-ordering-coerce*`,
`*h2-ordering-stringp*`, `*h2-ordering-string-lt*`, `*h2-ordering-symbolp*`,
`*h2-ordering-iff*`, `*h2-ordering-symbol-lt*` and `*h2-ordering-list-lt*`
are prover symbols. `*h2-ordering-character-order*` lists rule names in
their search order.

| ACL2 call | Result |
|---|---|
| `(h2-ordering-eql-on-conses proof)` | `(cons name proof)` for the equality-by-parts fact. |
| `(h2-ordering-character-list-order proof theorem formula)` | `(cons step proof)` for the theorem named by the ASCII string `theorem` and expressed by `formula`. |
| `(h2-ordering-character-list-trichotomy proof formula)` | `(cons step proof)` for the character list trichotomy formula. |
| `(h2-ordering-coerce-list value)` | The term coercing the term `value` to a list. |
| `(h2-ordering-equality-value proof test evidence)` | Step giving the Boolean value of the equality term `test` using the evidence Step. |
| `(h2-ordering-equal-tests proof left right forward backward)` | Step equating the equality terms `left` and `right`, given evidence Steps for each implication. |
| `(h2-ordering-coerce-injective proof)` | `(cons name proof)` for the injectivity fact about coercion of strings. |
| `(h2-ordering-string-asymmetry proof)` | `(cons name proof)` for string asymmetry. |
| `(h2-ordering-string-trichotomy proof)` | `(cons name proof)` for string trichotomy. |
| `(h2-ordering-symbol-trichotomy proof formula)` | `(cons step proof)` for the symbol trichotomy formula. |
| `(h2-ordering-symbol-order proof theorem formula)` | `(cons step proof)` for the named symbol theorem and its formula. |

Names in results are ASCII strings. A Step or name position can hold a
failure. The Search in a result pair contains the settings and auxiliary
entries established by the call. `h2-ordering-coerce-list` constructs its
term directly.

`proof` uses the Search representation in `prover/h2/sig/search.md`.
`equality-value` and `equal-tests` also accept a plain Library or Proof.
A Search hook request can appear in the value position of a pair. The
Search retains its unconsumed replies.
