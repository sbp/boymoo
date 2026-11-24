# Proper list recognizers

A Library and a Step have the forms in their respective signatures. A term is
a prover term. Evidence is a list of Steps. The constants
`*proper-lists-true-list*` and `*proper-lists-list-types*` are the
`TRUE-LISTP` symbol and the list of element recognizer symbols, respectively.

Each function below returns `(cons result library)`, with the Library as it
stands on return. A completed result can be a failure. `nil` means the
tactic supplied no proof.

| Function | Arguments in order | Result |
| --- | --- | --- |
| `proper-lists-proper-list-rule` | Library, predicate symbol | Name string for the predicate's proper-list lemma, or `nil` |
| `proper-lists-cons-type-rule` | Library, predicate symbol | Name string for the predicate's cons lemma, or `nil` |
| `proper-lists-expose-cons-type` | Library, formula term, evidence | Step exposing a list recognizer applied to a constructed list, or `nil` |
| `proper-lists-proper-list-search` | Library, value term, evidence | Step proving the value is a proper list, `nil`, or a request |
| `proper-lists-proper-list-search-resume` | Library, continuation, answer | Same results as `proper-lists-proper-list-search` |

A request is `(:call goal nil continuation)`. The caller searches its
evidence for `goal` and passes the answer and resulting Library to the
continuation. Repeat until the result is a Step, `nil`, or a failure.
