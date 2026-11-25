# Evaluator constraints

`lib` is a Library as specified in `library.md`. An Evaluator is
`(:evaluator lib ops name eval eval-list apply formulas)`. The three
function names `eval`, `eval-list` and `apply` are terms. `name` is their
shared string label. `ops` is an ordered list of `(operator meaning numbers)`.
Its fields are a quoted symbol, a term and the distinct argument indices
used by the term. The indices are ordered by their decimal spelling.
`formulas` is the list of witness constraint terms.
`evaluator-proofs-evaluator-make` takes the seven fields in order.
The field accessors have the prefix `evaluator-proofs-evaluator-`
followed by the field name.

`data` has the form `(functions named-formulas)`, with
`(symbol arity)` entries in `functions` and `(name formula)` entries
in `named-formulas`. The constraints specify a term evaluator and a
list evaluator in that order. Evidence is a list of Steps for the
reduction and replay functions. In `evaluator-proofs-evaluator-add-shape-facts`
it is an alist from literals to Steps in insertion order.
`definitions` lists functions that the reducer may open. `logical`
selects the use of Boolean rules.

| ACL2 call | Result |
|---|---|
| `(evaluator-proofs-argument term index)` | The `CAR` of `term` after `index` applications of `CDR`, with an integer index. |
| `(evaluator-proofs-argument-number term)` | The positional index read from a term selecting an evaluator argument, or `unproved` for a different selector. |
| `(evaluator-proofs-operations functions formulas)` | The ordered list of operations, or `unproved` for an unrecognized evaluator shape. |
| `(evaluator-proofs-operations-abstract term used eval-term)` | `(cons meaning used)` with the abstracted operation term and the sorted distinct indices. `eval-term` is the original term evaluator symbol. |
| `(evaluator-proofs-evaluator-init lib data)` | The Evaluator with witness names and the substituted formulas. |
| `(evaluator-proofs-evaluator-opened evaluator call evidence definitions logical)` | A Step unfolding and reducing the function call `call`. |
| `(evaluator-proofs-evaluator-list-equation evaluator term env evidence)` | A Step unfolding and reducing list evaluation on `term` and environment `env`. |
| `(evaluator-proofs-evaluator-projection evaluator index)` | The Evaluator with the argument projection lemma for `index` added. |
| `(evaluator-proofs-evaluator-list-replay evaluator)` | The Evaluator with the quoted values lemma added. |
| `(evaluator-proofs-evaluator-replay evaluator goal evidence)` | A Step proving the replay equality `goal`. |
| `(evaluator-proofs-evaluator-add-shape-facts evaluator evidence)` | The evidence alist with the derived shape facts added or replaced. |
| `(evaluator-proofs-evaluator-constraint evaluator position formula)` | A Step proving the constraint `formula` at its zero-based `position`. |
| `(evaluator-proofs-evaluator-witness evaluator first)` | `(cons entry evaluator)` with the witness proof entry for `first` and the Evaluator containing its updated Library. |
| `(evaluator-proofs-evaluator-witnesses lib data)` | `(cons entry lib)` with the witness proof entry and the Library containing its definitions and lemmas. |

The constructor and field accessors for the record do not return a failure. Each computation may return a failure in place of its result where a proof or its shape is unavailable. The constants `*evaluator-proofs-a*`, `*evaluator-proofs-b*`, `*evaluator-proofs-symbolp*`, `*evaluator-proofs-quoted*`, `*evaluator-proofs-kwote*`, `*evaluator-proofs-kwote-list*`, `*evaluator-proofs-pairlis*`, and `*evaluator-proofs-function*` are the environment variables, symbols, quoted symbol, and operation selector used in the evaluator terms.

`witness` and `evaluator-witnesses` put a failure in their entry position, preserving the Evaluator or Library reached by the call.

`(evaluator-proofs-fields-of-size fields size)` accepts fields of the
required size or returns a failure. `(evaluator-proofs-formulas named-formulas)`
returns the formula terms in order, or a failure for a malformed pair.

`(evaluator-proofs-argument-index index)` accepts integers, gives
`0` for `nil` and `1` for `t`, and returns a failure for other values.
