# Book termination measures

`lib` is a Library as specified in `prover/sig/library.md`. `search` is a
theorem search as specified in `prover/t3/sig/book-theorems.md`. Definitions,
ruler extenders, Calls, and name-to-measure alists follow
`prover/sig/termination.md`. `stored` is a name-to-measure alist. An ordinality
case passes `nil` for `call`. A `clause` is a list of literals in source
order. `evidence` is an Evidence object as specified in
`prover/t3/sig/logic.md`. Terms and Steps follow `prover/sig/proof.md`. A proof
entry has the form returned by `proof-proof-entry`.

| Call | Result | Failure |
|---|---|---|
| `(t3-book-measures-count-or-length lib smaller larger evidence)` | `(cons step evidence)` with a size-comparison Step for the two measure terms and the resulting Evidence. | `unsupported` when the size comparison is unavailable, or a construction failure. |
| `(t3-book-measures-sum-decrease lib smaller larger evidence)` | `(cons step evidence)` with a decrease Step for the two measure terms and the resulting Evidence. | `unsupported` or a construction failure. |
| `(t3-book-measures-prove-clause lib search clause call)` | `(list step lib search)` with the proof Step for the clause and the resulting Library and theorem search states. | A failure from the search or proof construction. |
| `(t3-book-measures-measure-proof lib search rulers definitions stored)` | `(list entry lib search)` with the measure proof entry and the resulting Library and theorem search states. | The original termination failure if no fallback plan succeeds, or a construction failure. |

Failures are the entire result. An updated theorem search retains its
index and reflects the Library and fuel reached by the search.
