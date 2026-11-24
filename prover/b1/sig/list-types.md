# Types of list operations

`lib` is a Library as specified in `prover/sig/library.md`. Terms and Steps
have the forms described in `prover/sig/proof.md`. Each call can return a
failure from reading terms or constructing a proof. A failure is the entire
result.

| Call | Result |
|---|---|
| `(b1-list-types-typed-head-and-tail lib list-type cons)` | A two-element list of Steps for the type of the head and the type of the tail, given the list type Step `list-type` and the positive `CONSP` Step `cons`. |
| `(b1-list-types-typed-cons lib predicate pair head tail)` | Step for `predicate` applied to construction term `pair`, using the type Steps `head` and `tail` for its components. |
| `(b1-list-types-typed-empty lib predicate)` | Step for `predicate` applied to quoted `NIL`. |
| `(b1-list-types-numeric-fold-type lib formula)` | Step for the type of the result of the numeric list fold in `formula`. |
| `(b1-list-types-natural-excess lib formula)` | `(cons step lib)` with the Step for the natural result in `formula`, and the Library with the lemma for `MAXLIST` added if needed. |
| `(b1-list-types-numeric-insert-type lib formula)` | Step for the list type preserved by the insertion in `formula`. |
| `(b1-list-types-numeric-sort-type lib formula)` | Step for the list type preserved by the sort in `formula`. |

The term constants are `*b1-list-types-min*`, `*b1-list-types-max*`,
`*b1-list-types-maxlist*`, and `*b1-list-types-natural-list*`.
