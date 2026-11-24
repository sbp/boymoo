# Array compression

`proof` is the H2 proof search object for book statements. Terms and Steps
use the forms in `prover/sig/proof.md`. A recognizer is a list consisting of
the recognizer symbol followed by its parameters other than the data. A
law is identified by its ASCII fact name. The `laws` argument contains the
constructor, lookup, reversal, and loop names in that order.

Each function can return a failure. Where the result is `(cons value proof)`,
the proof contains any facts, entries, and search settings established by
the call. All binding lists and evidence lists preserve their order.

| Function | Arguments in order | Result |
|---|---|---|
| `h2-compression-range-decrease` | `proof`, index term, limit term, Step proving the loop is active | `(cons step proof)` for the decrease in the remaining range. |
| `h2-compression-logical-branch` | `proof`, opened term, Step selecting the conditional branch | The equality Step for the selected body after removing wrappers. |
| `h2-compression-loop-name` | `proof` | `(cons name proof)` for the compression loop name independence law. |
| `h2-compression-normalize-compression` | `proof`, theorem formula | `(cons step proof)` for the compression normalization theorem. |
| `h2-compression-loop-preserved` | `proof`, recognizer, constructor law name, lookup law name | `(cons name proof)` for the loop preservation law. |
| `h2-compression-compression-laws` | `proof`, recognizer | `(cons laws proof)` with the four names in the order above. |
| `h2-compression-compressed-conforms` | `proof`, recognizer, compression term, source recognizer Step, header Step, `laws` | A Step proving that the compressed alist satisfies the recognizer. |
| `h2-compression-compressed-conforms-checked` | Leaf value term, list of signed tests, `proof`, source data term, source recognizer Step, recognizer, constructor law name, reversal law name, loop law name, header recognizer Step | The recognizer Step for that leaf. |
| `h2-compression-absent-compression` | `proof`, compression term, Step for an absent header | `(cons step proof)` for the empty compressed data. |
| `h2-compression-compression-list-theorem` | `proof`, theorem label string, theorem formula | `(cons step proof)` for the alist or bounded alist theorem. |
| `h2-compression-compressed-array` | `proof`, theorem formula, header preservation law name | `(cons step proof)` for the array recognizer theorem. |

The term constants are `*h2-compression-compress-loop*`,
`*h2-compression-zp*`, `*h2-compression-name*`, `*h2-compression-data*`,
`*h2-compression-index*`, `*h2-compression-limit*`,
`*h2-compression-default*`, `*h2-compression-canonical-name*`, and
`*h2-compression-header*`.

Pass the inherited Search from `prover/h2/sig/search.md` as `proof`. An
inherited method can return a Search request in place of the result. Append
the method reply and repeat the original call as specified there. A Search
that dispatches the `:set-fuel` method also receives the argument `(42000)`
where a recipe updates the BookProof rewriting budget. Reply with
`(:return nil)` after setting the budget.
