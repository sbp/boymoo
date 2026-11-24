# Witnesses for constrained functions

Terms, Steps and Libraries use the forms in `prover/sig/proof.md` and
`prover/sig/library.md`. `formulas` is a list of `(name term)` pairs in the
order in which the constraints appear. A renaming map is an alist of
`(original . replacement)` pairs in insertion order. Only function heads
are renamed, including heads in lambda bodies.

A successful witness recipe returns `(cons (list names proofs) lib)`.
The names are witness symbols in constrained-function order. The proof
Steps are in constraint order. The returned Library contains the
definitions and lemmas installed by the recipe. A failed recipe returns
its failure directly.

| ACL2 call | Arguments and result | Failure |
|---|---|---|
| `(b1-witnesses-rename-calls term names)` | A term and a renaming map. Returns the renamed term. | A failure for an incomplete lambda head or empty compound term. |
| `(b1-witnesses-identity-witness lib functions formulas)` | A Library, constrained function symbols and their constraint formulas. Returns the witness result with `G14`. | A failure from reading or proving a constraint. |
| `(b1-witnesses-successor-witness lib functions formulas)` | The same arguments. Returns the witness result with the successor and constant-true witnesses. | A failure from reading or proving a constraint. |
| `(b1-witnesses-recognizer-witness-proofs lib formulas names wrappers)` | A Library, constraint formulas, renaming map and list of wrapper symbols to unfold. Returns a list of Steps in constraint order. | A failure from reading or proving a constraint. |
| `(b1-witnesses-alist-type-witness lib functions formulas)` | A Library, constrained function symbols and their constraint formulas. Returns the witness result for abstract association lists. | A failure from reading or proving a constraint. |
| `(b1-witnesses-list-type-witness lib functions formulas)` | The same arguments. Returns the witness result for an abstract list recognizer. | A failure from reading or proving a constraint. |
| `(b1-witnesses-evaluator-witness lib functions formulas)` | The same arguments. Returns the witness result for a term and list evaluator. | A failure from reading or proving a constraint. |
| `(b1-witnesses-small-witnesses lib functions formulas index)` | A Library, list of `(symbol arity)` pairs, constraint formulas and the search FactIndex. Returns the first successful witness result. | `Unproved` when no trial succeeds, or another failure from reading a constraint or constructing a proof. |

`*b1-witnesses-witnesses*` is an ordered alist from unqualified ASCII
function names to the ACL2 symbols naming the
corresponding witness recipes in the table. Both `E1` and `G16-WITNESS`
are looked up by their unqualified names, like the other constraints.

`b1-witnesses-small-witnesses-candidates` constructs and tries one
candidate at a time. It stops at the first success or when it encounters
a failure it must propagate.

## Library carried by a recipe

`b1-witnesses-successor-witness-with-library`,
`b1-witnesses-alist-type-witness-with-library`,
`b1-witnesses-list-type-witness-with-library` and
`b1-witnesses-evaluator-witness-with-library` take the arguments of their
respective recipes. Each returns `(cons value lib)` on both success and
error. On success `value` is `(names proofs)`. On error `value` is the
failure and `lib` retains the entries installed before it.

The evaluator variant carries the Library from completed evaluator calls.
