# H2 prover interface

`(h2-api-prove statement earlier library aids)` takes one ASCII statement
string and three lists of ASCII input lines. It returns `nil` when it has
no certificate, or `(lemmas entry)`. The `lemmas` are auxiliary entry
strings in dependency order, and `entry` is the statement's proof string.
Each string ends in a newline.

Auxiliary names consist of `PROVER-H2-`, the auxiliary name stem, and the
16 uppercase hexadecimal digits of its SipHash-2-4 digest. The digest
covers the certificate text with its dependencies' assigned names.

A parsed line is `(raw kind fields)`. `raw` ends in one LF after
normalization of trailing CR and LF characters. `kind` is a string.
The fields use the term representations in `prover/sig/proof.md`. Entry
records have the form `(kind name counts source)` from `prover/sig/library.md`.

A world is `(:h2-world library proof not-nil seen private earlier)`.
`library` is the supplied library line list. `proof` is the BookProof,
and `not-nil` is the underlying core Proof from the initialized library.
`seen` and `private` are sets of normalized lines and written private
names, ordered by escaped string keys. `earlier` is the last supplied
earlier list. Aid maps are insertion-ordered alists. Each hint value
contains distinct symbols in occurrence order.

| Function | Arguments and result | Failure |
|---|---|---|
| `h2-api-parse` | A raw line. Returns its parsed line. | Non-ASCII input or a statement that the reader cannot parse. |
| `h2-api-library` | Library lines. Returns `(proof seen private)` for the admitted library. | Failure while parsing or preparing the BookProof. |
| `h2-api-aids` | Aid lines. Returns `(measures hints)` with measures by function symbol and hints by obligation symbol. | Failure while parsing an aid or reading its fields. |
| `h2-api-world-init` | Library lines. Returns their world with an empty earlier prefix. | Library preparation failure. |
| `h2-api-world-advance` | A world and a complete earlier list that extends its earlier prefix. Returns the world after admitting the new suffix in input order. | Failure while parsing or admitting a line. |
| `h2-api-world-trial` | A world. Returns a proof trial with its rule index and conditional index lemmas. | Proof preparation failure. |
| `h2-api-world-with-indexed-prefix` | Library and earlier lines. Returns their world and can index the written names during admission. | World preparation failure. |
| `h2-api-namespaced` | Auxiliary and final entry records and a set of reserved names. Returns `(lemmas entry)` with their certificate names. | An invalid or occupied auxiliary name, non-ASCII proof text, or a proof writing failure. |
| `h2-api-namespaced-with-tree` | The same arguments and an additional tree of reserved names. | The same failures as `h2-api-namespaced`, with both sources of reserved names checked. |
| `h2-api-prove-internal` | The four interface arguments. Returns `(lemmas entry)` or `nil`. | Propagates an input or proof failure. |

`h2-api-make-world` takes the six fields in order. The accessors are
`h2-api-world-library`, `h2-api-world-proof`, `h2-api-world-not-nil`,
`h2-api-world-seen`, `h2-api-world-private`, and `h2-api-world-earlier`.

`(h2-api-string-tree-find key tree)` returns the matching node or `nil`.
Nodes have the form `(string height left right)` with an optional value at
the end. The keys use `string<` order. `h2-api-string-tree-has-p` tests
membership in the same tree.

`(h2-api-proof-trial proof)` prepares a trial from a BookProof.
`(h2-api-theorem-entries-from-proof proof trial data name measures hints)`
returns the theorem entries or a failure. When
`h2-api-special-fallback-p` recognizes the failure from the specialized
theorem tactic, the general tactic starts from a fresh trial of `proof`.
See `prover/h2/notes/failures.md` for the retry kinds.
