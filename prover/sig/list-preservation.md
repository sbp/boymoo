# List recognizer preservation

A Library and a Step have the forms in their respective signatures. A term is
a prover term. Evidence is a list of Steps. The constants
`*list-preservation-append*`, `*list-preservation-revappend*`,
`*list-preservation-list-combiners*` and `*list-preservation-true-list-fix*`
are the symbols for `BINARY-APPEND`, `REVAPPEND`, both operations in that
order, and `TRUE-LIST-FIX`, respectively.

Functions that return a pair return `(cons result library)`, with the
Library as it stands on return. A completed result can be a failure.
`nil` means the tactic supplied no proof.

| Function | Arguments in order | Result |
| --- | --- | --- |
| `list-preservation-combine-type-rule` | Library, predicate symbol, operation symbol | Pair with the lemma name string or `nil` |
| `list-preservation-preserve-list-type` | Library, formula term | Pair with a Step for the formula, `nil`, or a request |
| `list-preservation-preserve-list-type-resume` | Library, continuation, answer | Same results as `list-preservation-preserve-list-type` |
| `list-preservation-equate-conditions` | Library, left term, right term, test terms, evidence | Step for equality of the terms, or a failure |
| `list-preservation-combine-list-equation` | Library, formula term | Pair with a Step for the equation or `nil` |

A request is `(:call goal nil continuation)`. The caller proves the
requested goal and passes the Step or failure as `answer` together with
the resulting Library. Pass the continuation as returned. Repeat until
the result is a Step, `nil`, or a failure. The second proof request follows
the first successful answer.
