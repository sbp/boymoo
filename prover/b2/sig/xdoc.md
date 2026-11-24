# XDOC argument and tree predicates

Terms, Steps, and the Library have the forms in `prover/sig/proof.md` and
`prover/sig/library.md`. A pair is `(cons value library)` with the resulting
Library. A failure is the entire result. Evidence is a list of Steps in the
order supplied. Every function can return a failure when reading its inputs or
constructing the proof.

| Call | Result |
|---|---|
| `(b2-xdoc-cons-type library datum)` | The Step proving the cons term `datum` is a cons. |
| `(b2-xdoc-cons-excludes library predicate datum)` | The Step denying the predicate with symbol `predicate` on cons term `datum`. |
| `(b2-xdoc-argument-partition library formula)` | A pair with the Step proving the given argument partition type formula. |
| `(b2-xdoc-trees-cons library formula)` | The Step proving the given tree cons formula. |
| `(b2-xdoc-make-tree-tag library formula)` | The Step proving the given tree tag construction formula. |
| `(b2-xdoc-string-result n library value evidence)` | A pair with the Step proving term `value` has type `STRINGP`, using `evidence`. Pass `1000000` as the initial fuel and `nil` for default evidence. |
| `(b2-xdoc-tag-strings library formula)` | A pair with the Step proving the given string projection formula. |
| `(b2-xdoc-description library formula)` | A pair with the Step proving the given description string formula. |
| `(b2-xdoc-xdoc-theorem library name formula)` | A pair with the Step proving the XDOC theorem with symbol `name` and formula `formula`. |

The symbol constants are `*b2-xdoc-acons*`, `*b2-xdoc-keywordp*`,
`*b2-xdoc-stringp*`, `*b2-xdoc-coerce*`, `*b2-xdoc-append-str*`,
`*b2-xdoc-append-strs*`, `*b2-xdoc-treep*`, `*b2-xdoc-trees*`,
`*b2-xdoc-tree-tag*`, `*b2-xdoc-cons-tree*`, `*b2-xdoc-make-tag*`,
`*b2-xdoc-list-true*`, `*b2-xdoc-tag-left*`, and `*b2-xdoc-tag-right*`.
The set constants `*b2-xdoc-partition-types*` and `*b2-xdoc-xdoc-theorems*`
list their symbols in ascending order of their serialized forms.
