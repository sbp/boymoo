# Primitive badge table certificate

`p` is the Tactics object defined in `tactics.md`. Symbols, data, and Steps use the forms in `prover/sig/proof.md`. A failure occupies the entire result. The `table` is a list of badge entries in lookup order. Each entry is a cons datum with a symbol datum as its first element. `wanted` and `excluded` are lists of symbol data in input order.

| ACL2 call | Result and failures |
|---|---|
| `(h4-badge-table-selector offset)` | The term selecting the character at integer `offset` from `CHARS`. Negative offsets give the same term as zero. |
| `(h4-badge-table-name-filter p wanted excluded)` | `(cons filters p)` with newly defined test names in definition order followed by the filter name. May return a failure. |
| `(h4-badge-table-table-filter p excluded)` | `(cons filters p)` with the set of newly defined test names and the filter name. The set is an ordered list of distinct names sorted by their textual encoding. May return a failure. |
| `(h4-badge-table-lookup-miss p)` | A Step for dropping a table entry with a different key. May return a failure. |
| `(h4-badge-table-exclude-entry p entry rest premise filters)` | A Step for skipping `entry` with the term `rest` as tail, using the hypothesis Step `premise` and the filter names. May return a failure. |
| `(h4-badge-table-lookup-chunk p table low high filters previous old-suffix new-suffix)` | A Step for an interval with inclusive integer `low` and exclusive integer `high`. `previous` and `new-suffix` are fact names. `old-suffix` is a fact name or `nil` for the first chunk. May return a failure. |
| `(h4-badge-table-certify p wanted)` | `(cons filters p)` with the updated Tactics object containing definitions and certificate lemmas in emission order. Pass `:none` to use the default names or `nil` for an empty list of wanted names. The emitter is the interface's operation that inserts the fact and appends the lemma entry. May return a failure. |

The constants are `*h4-badge-table-hons*`, `*h4-badge-table-hons-equal*`, `*h4-badge-table-miss*`, `*h4-badge-table-chars*`, `*h4-badge-table-name*`, `*h4-badge-table-badge-value*`, `*h4-badge-table-rest*`, `*h4-badge-table-atom*`, `*h4-badge-table-char-code*`, `*h4-badge-table-less*`, and `*h4-badge-table-chunk-size*`.
