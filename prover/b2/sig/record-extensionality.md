# Record extensionality

`lib` is a Library. Records, keys, formulas, and goals are prover terms. Evidence is a list of Steps in the supplied order. The symbols `*b2-record-extensionality-difference*`, `*b2-record-extensionality-above*`, `*b2-record-extensionality-witness*`, `*b2-record-extensionality-u*`, `*b2-record-extensionality-e*`, `*b2-record-extensionality-get*`, `*b2-record-extensionality-set*`, and `*b2-record-extensionality-get-update*` name the difference function, its lemmas, variables, the record operations, and the update lemma. `*b2-record-extensionality-extensional*` is the set of theorem names, ordered by the text of their serialized symbols.

| Call | Result |
|---|---|
| `(b2-record-extensionality-install-difference lib)` | The resulting Library, with the difference definition and measure entries installed when absent. |
| `(b2-record-extensionality-contradict lib goal first second)` | The Step for `goal` by cutting the contradictory Steps `first` and `second`. |
| `(b2-record-extensionality-different-tails lib facts)` | The Step stating that the record tails differ, from the evidence `facts`. |
| `(b2-record-extensionality-after-head lib start head record before bound)` | The order-or-empty Step for `record`, from the order Steps `before` and `bound`. |
| `(b2-record-extensionality-self-comparison lib key-value)` | The irreflexivity Step for the key. |
| `(b2-record-extensionality-first-key-laws lib lookup-key record-key order)` | The two Steps for reverse order and distinctness, in that order, from the Step `order`. |
| `(b2-record-extensionality-difference-lemma lib is-bound)` | The resulting Library with the requested difference lemma. `is-bound` selects the bound lemma when true and the witness lemma when false. |
| `(b2-record-extensionality-updated-lookup lib lookup-key left right premise)` | The Step equating the two lookups, with a premise Step or `nil`. |
| `(b2-record-extensionality-record-extensionality lib name formula)` | `(cons step lib)` with the Step for theorem symbol `name` and its resulting Library. |

Each function can return a failure as its entire result. The callback-taking helpers `pair_cases` and `equal_from_lookups` are local to this book.
