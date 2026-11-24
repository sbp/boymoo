# Removing progn wrappers

A Library and a Step have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. Evidence has the form in `prover/t3/sig/logic.md`.
RemoveProgn uses the TermTraversal representation from
`prover/t3/sig/book-substitution.md` with calls for `REMOVE-PROGN` and
`REMOVE-PROGN-LST`, and the quoted true term as its environment.

Each function can return a failure from constructing its proof or reading its
arguments. In that case the failure is the entire result.

| Call | Arguments and result |
|---|---|
| `(t3-book-remove-progn-remove-progn-init lib)` | The RemoveProgn traversal for Library `lib`. |
| `(t3-book-remove-progn-remove-progn-term-result self value typed evidence)` | List of the Step for the branch value `value` under type Step `typed`, the resulting traversal, and the resulting Evidence. |
| `(t3-book-remove-progn-remove-progn-term-result-head new-head tests self typed updated length known original args evidence)` | Pair of the branch Step and the resulting traversal. `new-head` and `args` are terms, `tests` are signed tests, `typed`, `updated`, `length` and `original` are Steps, and `known` is the premise Step list. |
| `(t3-book-remove-progn-removal lib name formula)` | Pair of the removal theorem entry and the Library with its auxiliary definition and lemma. |

The term constants are `*t3-book-remove-progn-remove*`,
`*t3-book-remove-progn-remove-list*` and `*t3-book-remove-progn-lambda-shape*`.

The traversal has kind `:base` and a false multivalue field.
