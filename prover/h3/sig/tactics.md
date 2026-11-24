# Slice theorem tactics

A Library, a term and a Step have the forms in `prover/sig/library.md`
and `prover/sig/proof.md`. A Search and its context have the forms in
`prover/h3/sig/rewrite.md`. Definition and call arguments are lists in argument
order. The names of facts are prover symbols or strings, and theorem labels
are strings without the package. Hypotheses are a list of Steps.

| Call | Result |
|---|---|
| `(h3-tactics-solve library name formula)` | `(cons step library)` with the proof of the formula and the Library containing any auxiliary lemmas. |
| `(h3-tactics-using library formula names definitions calls hypotheses budget)` | Step from proof search with the given fact names, definitions, calls, hypotheses and initial case budget. Use `nil` for an empty input list and 150 for the ordinary case budget. |
| `(h3-tactics-convert-fact library formula name definitions)` | Step from the named fact, specialized after reduction with the given definitions. |
| `(h3-tactics-parallel-recursions library formula)` | Step from structural induction on the shared list argument of the two calls. |
| `(h3-tactics-parallel-recursions-prove-case hypotheses library formula left right)` | Step proving a case of parallel recursion; `left` and `right` are the two calls in the formula. |
| `(h3-tactics-character-list-idempotent library formula)` | Step from structural induction on the character-list argument. |
| `(h3-tactics-character-list-idempotent-prove-case hypotheses library formula calls)` | Step proving a case of character-list idempotence; `calls` lists the permitted openings. |
| `(h3-tactics-completion library name formula)` | Step for the named completion formula. |
| `(h3-tactics-complex-default-second library formula completed search context)` | Step for the second complex completion, given the first completion Step and its Search and context. |
| `(h3-tactics-structural-shape library formula)` | `(cons step library)` with the structural proof and any auxiliary lemmas, or with a nil Step when no shape matches. |

Every entry can return a failure as its entire result. The absence of a
tactic in `h3-tactics-solve` failures `Unproved`. The dictionaries
`*h3-tactics-context-types*`, `*h3-tactics-direct*` and
`*h3-tactics-completions*` follow the order of their declarations. The other constants
are `*h3-tactics-atom*`, `*h3-tactics-endp*`, `*h3-tactics-numeric-equal*`,
`*h3-tactics-fix*`, `*h3-tactics-realfix*`, `*h3-tactics-dfp*`,
`*h3-tactics-to-df*`, `*h3-tactics-make-chars*`, `*h3-tactics-common-rules*`,
`*h3-tactics-logical*` and `*h3-tactics-intersections*`.
