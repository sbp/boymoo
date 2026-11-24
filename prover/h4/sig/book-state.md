# Indexed list state

Terms and Steps use the forms in `prover/sig/proof.md`. A library has the
form in `prover/sig/library.md` and supplies the proof methods for the state.

An IndexedState has the form
`(:h4-indexed-state library read write lookup overwrite commute identity evidence)`.
Read and write are function symbols. The next four fields are the names of
the corresponding laws, in the order supplied to the constructor. Evidence
is an insertion-ordered dictionary from first literals to Steps.

| Function | Arguments in order | Result | Failure |
|---|---|---|---|
| `h4-book-state-equation-instance` | Library, law name, target term, evidence Step list | Instance of the law's equation whose left side matches the term | A missing fact or premise, a failed match, or a failure from proof construction |
| `h4-book-state-indexed-state-init` | Library, read name, write name, four law names, evidence dictionary | IndexedState | A failure if the law list does not contain four names |
| `h4-book-state-indexed-state-on-write` | IndexedState, law name, target term | Equation instance using the state's evidence values in dictionary order | A failure from the instance |
| `h4-book-state-indexed-state-reduce` | IndexedState, term | Lookup or overwrite Step, or `nil` if neither law applies | A failure from a required premise or proof construction |
| `h4-book-state-indexed-state-restore` | Natural-number fuel, IndexedState, update term, original state term | Step restoring one slot through the intervening writes | A failure from proof construction, a failed assertion, or `Fuel` |
| `h4-book-state-indexed-state-invariant-equation` | IndexedState, law name, view function, written state term | Instance of the law on the view applied to the written state | A failure from the instance |

Pass `1000000` as the initial fuel for restoration. Pass `nil` for omitted
evidence. The accessors `h4-book-state-indexed-state-p`,
`h4-book-state-indexed-state-read`, `h4-book-state-indexed-state-write`,
`h4-book-state-indexed-state-lookup`,
`h4-book-state-indexed-state-overwrite`,
`h4-book-state-indexed-state-commute`,
`h4-book-state-indexed-state-identity`, and
`h4-book-state-indexed-state-evidence` each take the IndexedState and return
the indicated field without a failure.
