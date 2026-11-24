# Book termination

`proof` is the H1 prover. Terms and Steps have their forms in `prover/sig/proof.md`. Definitions, Calls and signed tests have their forms in `prover/sig/termination.md`. The `stored` dictionary maps each definition name to `(measure relation)`.

A Rulers object has the form `(:h1-rulers hypotheses search context)`. `hypotheses` is a Hypotheses object as in `prover/sig/descent.md`. `search` and `context` are the H1 Search and Context objects. All dictionaries are alists in insertion order. Rulers queries carry the updated Rulers object in the cdr of their result.

| Function | Arguments in order | Result |
|---|---|---|
| `h1-book-termination-rulers-init` | `proof`, signed test list | Rulers. |
| `h1-book-termination-rulers-add-logical-test` | Rulers, test term, Boolean `holds` | Updated Rulers. |
| `h1-book-termination-rulers-record` | Rulers, Step | Updated Rulers. |
| `h1-book-termination-rulers-find` | Rulers, term | `(cons step rulers)`, with `nil` when the step is absent. |
| `h1-book-termination-rulers-require` | Rulers, term | `(cons step rulers)`, or `CandidateRejected` when the step is absent. |
| `h1-book-termination-install-selector-tests` | `proof` | Updated prover with the selector and length rules. |
| `h1-book-termination-cons-from-nonatom` | `proof`, Step whose first literal denies an `ATOM` or `ENDP` test | Step proving `CONSP`. |
| `h1-book-termination-endp-noncons` | `proof`, Step proving `ENDP` | Step denying `CONSP`. |
| `h1-book-termination-cons-implies-truth` | `proof`, term, Step proving `CONSP` of that term | Step proving the term. |
| `h1-book-termination-positive-cons-count` | `proof`, term, Step proving `CONSP` of that term | Step proving its count is positive. |
| `h1-book-termination-count-descent` | `proof`, obligation clause, Call | Step proving the count decrease. |
| `h1-book-termination-next-position` | `proof`, child measure, parent measure, Call | Step proving the positional decrease. |
| `h1-book-termination-prove-measure-clause` | `proof`, obligation clause, Call or `nil` for ordinality | Step proving the obligation. |
| `h1-book-termination-bounded-measure-plan` | Definition list, Call list, measure dictionary | Measure dictionary using `NFIX`, or `:none` if unavailable. |
| `h1-book-termination-proof-measures` | `proof`, definition list, Call list, `stored` | Candidate measure dictionaries in candidate order. |
| `h1-book-termination-termination-entry` | `proof`, definition list, Call list, `stored` | Measure entry in the form returned by `proof-proof-entry`. |

Every function can return a failure as its entire result. `termination-entry` tries measure candidates in candidate order and returns the first successful entry, or `Unproved` if none succeeds. A candidate not reached by this search does not affect the result.

`(h1-book-termination-make-rulers hypotheses search context)` constructs the Rulers object. `h1-book-termination-rulers-hypotheses`, `h1-book-termination-rulers-search`, and `h1-book-termination-rulers-context` read its three fields. `h1-book-termination-rulers-with-context` replaces the Context and takes its current Search. These operations return their listed results.

`proof-measures` and `termination-entry` take a BookProver so the search can read its set of available function names.
