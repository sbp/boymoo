# Stored measures and structural decreases

`p` is a Library as specified in `prover/sig/library.md`. Definitions
and Calls have the forms in `prover/sig/termination.md`. A signed test is
`(term holds)` and a clause is an ordered list of literals. `aids` is
an insertion-ordered alist from a function name to its list of
`(measure relation)` pairs in aid order. A function-name set is a list
of distinct names used for membership tests.

| ACL2 call | Arguments and result | Failure |
|---|---|---|
| `(h4-book-measures-rule-tests p tests)` | Steps obtained from the signed tests and their consequences, in evidence insertion order. | Yes. |
| `(h4-book-measures-expand-evidence p premises)` | Steps obtained by expanding the ordered premise Steps, in evidence insertion order. The pending list is consumed from its end. | Yes. |
| `(h4-book-measures-measure-plans definitions calls aids)` | List of candidate measure lists. Stored plans use Cartesian product order, then the structural plan and the single-definition fallback plans in formal order. | Yes. |
| `(h4-book-measures-well-formed-measure term formals functions)` | Whether a measure uses the given formals and members of the function-name set. | A malformed lambda or application can return a failure. |
| `(h4-book-measures-structural-decrease p goal context)` | Step for an ordinal comparison using the supplied Descent Hypotheses. | `unproved` or a proof-operation failure. |
| `(h4-book-measures-decrease p clause tests splits)` | Step for the final literal of the clause, using signed tests and the integer split count. Pass `2` for the usual search. | Yes. |
| `(h4-book-measures-termination-proof p definitions calls aids book-functions)` | Two-element list of the first successful measure plan and the conclusion Steps in distinct clause order. `book-functions` is the set of constrained and chosen function names. | `unproved` when the attempts are exhausted. Failures outside the measure fallback kinds propagate. |

`unproved` has the form `(:failure "unproved" "")`. The constants `*h4-book-measures-wrappers*` and
`*h4-book-measures-selectors*` list the corresponding function names in
source order. The symbol constants are `*h4-book-measures-o-finp*`,
`*h4-book-measures-o-rst*`, `*h4-book-measures-o-first-expt*`,
`*h4-book-measures-o-first-coeff*`, `*h4-book-measures-atom*`,
`*h4-book-measures-endp*`, `*h4-book-measures-eq*`,
`*h4-book-measures-eql*` and `*h4-book-measures-num-eq*`.

## Inherited proof operations

These operations use the H4 constant rules. The `proof` parameter is the
Proof component of the Library. All of these operations can return a
failure.

| ACL2 call | Result |
|---|---|
| `(h4-book-measures-simplify proof term evidence definitions)` | An equality Step for the simplified term, or `nil`. |
| `(h4-book-measures-simplify-first proof step evidence definitions)` | The Step with its first literal simplified when possible. |
| `(h4-book-measures-prove proof term evidence definitions)` | A Step proving the term. |
| `(h4-book-measures-natural p term)` | A Step proving that the term is natural. |
| `(h4-book-measures-selector-decrease p goal context)` | `(cons step context)`, using signed tests and H4 constant rules in proving the ordinal comparison. |
