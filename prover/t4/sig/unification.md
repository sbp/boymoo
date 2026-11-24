# One-way unification measures

Terms and Steps have the forms in `prover/sig/proof.md`. `lib` is a Library
as specified in `prover/sig/library.md`. `definitions` is the list of
`(name formals body)` definitions, and `call` is a recursive Call, both
as specified in `prover/sig/termination.md`. `evidence` is Structural
Evidence as specified in `prover/t4/sig/structural.md`.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t4-unification-measures definitions)` | The dictionary from function names to their pattern-size measures, as an association list with entries `(name . measure)` in the order of first occurrence of the names. | A failure from reading a definition or its formals. |
| `(t4-unification-descent lib goal call)` | `(cons step lib)` with the measure comparison Step for `goal` and the Library with any lemmas added by the comparison. | A failure from reading a term or constructing a proof. |
| `(t4-unification-boolean-count lib test obj evidence)` | Library, equality test term, parent term and Evidence. Returns `(cons step lib)` proving the test result smaller than the parent. | A failure from reading a term or constructing a proof. |
| `(t4-unification-subproblem-bound lib field parent evidence)` | Library, projection term for field zero or two, pattern term and Evidence. Returns `(cons step lib)` with the strict bound for that field. | A failure from reading a term or constructing a proof. |

A failure is the entire result. The function names are also available as
`*t4-unification-unify*`, `*t4-unification-unify-list*`,
`*t4-unification-unify-equal1*`, `*t4-unification-unify-equal*`,
`*t4-unification-quoted-subproblems*`, `*t4-unification-mv-nth*` and
`*t4-unification-zp*`. The lists `*t4-unification-pairs*` and
`*t4-unification-fields*` list the pairs and fields in traversal order.
