# Projected list results

`lib` is a Library. Terms and Steps have the forms in `prover/sig/proof.md`.
`*t3-book-projections-mv-nth*` and `*t3-book-projections-alistp*` are ACL2
symbols. `*t3-book-projections-acons*` is a Common Lisp symbol.

A children map is an association list from actual child terms to ordered
lists of induction bindings. Keys stay in the order of discovery, retaining
their positions if found again. An observed map has projected terms as keys
and `(child pairs)` as values, in the order of the children map.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t3-book-projections-project lib index value)` | A Step for projection number `index` of term `value` with `MV-NTH`. | A failure from reading a term or constructing the Step. |
| `(t3-book-projections-recursive-tails lib call)` | `(variable children)` for the single list argument changed to its tails by the recursive calls of term `call`, or `nil` when the pattern does not apply. | A failure from reading or substituting a term. |
| `(t3-book-projections-projected-list lib formula)` | A Step proving `formula` by induction on the recursive input, or `nil` when the pattern does not apply. | `Unsupported` when a selected value has no list proof, or a failure from constructing the Step. |
| `(t3-book-projections-projected-list-leaf value tests lib index observed variable accepted predicate measure formula)` | A leaf Step under signed `tests`. `index` is a quoted integer, `variable` is the recursive input, `accepted` is the Step for its list hypothesis or `nil`, `predicate` is the projected result's list predicate, and `measure` and `formula` are the induction terms. | A failure from constructing the Step. |
| `(t3-book-projections-projected-list-leaf-tail-proof value lib variable accepted evidence)` | `(cons step evidence)` for the list type of tail term `value`, using `accepted` and the supplied Evidence. | A failure from evidence or proof construction. |
| `(t3-book-projections-projected-list-leaf-recognize n value lib observed variable accepted predicate measure formula evidence)` | `(cons step evidence)` for the list type of term `value`. Use `1000000` for initial fuel `n`. The remaining arguments have the forms of the leaf call. | `Fuel`, `Unsupported`, or a failure from evidence or proof construction. |

`t3-book-projections-project` starts with `1000000` recursive steps and
returns `(:failure "Fuel" "t3-book-projections-project")` on exhaustion.
