# Quoted finite tables

`proof` is the H2 proof search object. Terms and Steps have the forms in
`prover/sig/proof.md`. The constants `*h2-finite-member*` and
`*h2-finite-assoc*` denote `MEMBER-EQUAL` and `ASSOC-EQUAL`. Table contents
and keys retain their order and repetitions.

Each call returns `(cons value proof)`. The resulting object retains any
updated search settings and auxiliary lemmas. The value can be a failure.

| ACL2 call | Value |
|---|---|
| `(h2-finite-branch proof function key data)` | An equation Step for NIL data, or `(test yes no)` with the comparison and the branch equation Steps for a table cell. |
| `(h2-finite-table-property proof function key values template leaf)` | Step proving the template, with `*proof-result*` standing for the lookup value, under the hypothesis of a successful lookup. |
| `(h2-finite-table-inclusion proof key required available function)` | Step transporting membership of `key` along a subsequence of table keys. `function` is `*h2-finite-member*` for the standard membership proof. |
| `(h2-finite-member-of-constant proof formula)` | Step proving the lookup in `formula` at its quoted key. |
| `(h2-finite-lookup-data proof term function key)` | The unquoted table data of the indicated lookup after normalization. |
| `(h2-finite-character-proof proof theorem formula)` | Step proving `formula` by the finite table recipe for the ASCII theorem name `theorem`. |

For `table-property`, `leaf` is `:solve` for the proof search object's
solver or `:member-of-constant` for `h2-finite-member-of-constant`. An
external leaf function is represented by `(t reply ...)`, where each
reply is `(cons step proof)` in invocation order. When a reply is needed,
the value is `(:call :leaf proof formula)`. Compute the requested leaf and
repeat the original call with its reply appended. Leaf requests follow
the table from its last value to its first.

`proof` uses the Search representation in `prover/h2/sig/search.md`. A
Search hook request can appear in the value position. The Search retains
its unconsumed replies.
