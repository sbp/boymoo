# Structural list preservation

`lib` is a Library. `formula`, predicates, and argument variables are prover terms. Evidence is a list of Steps in the supplied order. The five recognizer symbols are `*b2-list-properties-true-list*`, `*b2-list-properties-pseudo-list*`, `*b2-list-properties-symbol-list*`, `*b2-list-properties-character-list*`, and `*b2-list-properties-strings*`. `*b2-list-properties-recognizers*` is their set, ordered by the text of the serialized symbols. A predicate collection is used for membership and can be supplied in any order.

| Call | Result |
|---|---|
| `(b2-list-properties-selector-evidence lib evidence predicates)` | The evidence after opening cons recognizers, in construction order. Pass `*b2-list-properties-recognizers*` for the default. |
| `(b2-list-properties-preserve-list lib formula position rules predicates search)` | The induction Step. `position` is the zero-based argument index, `rules` is the list of fact names in rule trial order, and `search` is a Search or `nil`. Pass `nil` for no rules and `*b2-list-properties-recognizers*` for the default predicate set. |
| `(b2-list-properties-preservation-plan lib formula)` | `nil` or `(position predicates)`, with the predicate set ordered by the text of the serialized symbols. |

The proof operations propagate a failure and can return `Unproved`. The plan can propagate a failure from reading a malformed term or analyzing recursive calls. Search state is shared across leaves in their visitation order. `(b2-list-properties-preserve-list-with-search lib formula position rules predicates search)` returns `(cons step updated-search)` for callers that need the resulting Search, or a failure.
