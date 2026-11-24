# Term transformations

Terms and symbols have the forms in `prover/sig/proof.md`. The selector constants are `*terms-car*` and `*terms-cdr*`.

| Function | Arguments in order | Result | Failure |
|---|---|---|---|
| `terms-replace-calls` | Term, association list with `(old-head . new-head)` entries | The term with function heads replaced, including inside lambda bodies | A malformed lambda head |
| `terms-selector-edges` | Term, base term | List of `(selector argument)` edges from the base to the term, or `nil` | A selector with no argument |

`terms-unproved-p` recognizes results that record an unsuccessful proof
attempt. `terms-proof-fallback-p` also recognizes failures that allow a
tactic to try a different proof. The failure kinds are documented in
`prover/notes/failures.md`.
