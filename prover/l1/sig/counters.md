# Counter measures

Terms, Steps, Library and Hypotheses use the shared representations.
The constants `*l1-counters-nfix*` and `*l1-counters-ten*` are the
`NFIX` symbol and quoted integer ten.

| Call | Arguments and result | Failure |
|---|---|---|
| `(l1-counters-strip-nfix term)` | Remove natural fixes along the outer sum of a term. | Malformed application. |
| `(l1-counters-counter-measure stored formals)` | Return a gap measure for the stored difference term and formal symbol list, or `nil`. | Malformed application. |
| `(l1-counters-integer-in-scope library term hypotheses)` | Return `(cons step hypotheses)` with an integrality proof for the term and the resulting Hypotheses. | Malformed term or proof construction. |
| `(l1-counters-multiply-advances library factor old old-integer old-positive)` | Return a strict advance Step for a quoted factor and old counter term, with Steps for integrality and positivity. | Malformed factor or proof construction. |
| `(l1-counters-advance library old new old-integer hypotheses)` | Return `(cons step hypotheses)` for the strict advance from old to new counter term, with the old term's integrality Step. The Step can be `nil`. | Malformed term or proof construction. |
| `(l1-counters-counter-decrease library goal hypotheses)` | Return `(cons step hypotheses)` for the ordinal comparison goal. The Step is `nil` if the tactic does not apply. Pass `nil` for an absent Hypotheses. | Malformed term or proof construction. |

Any failure replaces the entire result.
