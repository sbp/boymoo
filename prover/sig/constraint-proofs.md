# Constraint witnesses

`lib` is a Library and `index` a FactIndex, using the forms in `library.md` and `proof-search.md`. `function` is a function symbol, `arity` is its integer arity, and `formulas` is a list of constraint terms. `forbidden` and `names` are alists from original symbols to replacement symbols. `formals` is a list of formal variable terms, and a definition option is `(formals body)`.

| ACL2 call | Result |
|---|---|
| `(constraint-proofs-variables term)` | The set of free variable terms. |
| `(constraint-proofs-equational-options function arity formulas forbidden)` | The definition options from equations, in order. |
| `(constraint-proofs-fixer-options function formulas)` | The definition options from type fixer formulas, in order. |
| `(constraint-proofs-example-options lib index function formulas formals)` | The definition options from indexed example facts, in order. |
| `(constraint-proofs-options lib index function arity formulas forbidden)` | The definition options in search order, including the constant choices. |
| `(constraint-proofs-witness-candidate lib index functions formulas names definitions)` | `(cons entry lib)` for one combination of definitions. On ordinary search failure the entry is `nil`, and the candidate entries and facts are removed. `definitions` is a list of definition options. |
| `(constraint-proofs-construct-witnesses lib index data)` | `(cons entry lib)` for the first successful witness and its Library. The entry is `unproved` if the search exhausts its candidates. `data` contains `(functions named-formulas)`, with `(symbol arity)` entries in `functions` and `(name formula)` entries in `named-formulas`. |

Each function can return a failure. The equivalence symbol is `*constraint-proofs-iff*`.

The results that carry a Library put a failure in the entry position, preserving the Library reached by the call.

`construct-witnesses` visits combinations of the definition options in Cartesian product order and stops at the first successful entry.
