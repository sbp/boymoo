# Structural measures

Terms, Steps, Library, Calls and Hypotheses use the shared representations.
`*l1-structural-measures-atom*` and `*l1-structural-measures-endp*`
are the corresponding Common Lisp symbol data.

| Call | Arguments and result | Failure |
|---|---|---|
| `(l1-structural-measures-cons-evidence proof term hypotheses)` | Return `(cons step hypotheses)` with a Step that the term is a cons, or a `nil` Step. | Proof construction. |
| `(l1-structural-measures-selector-path term)` | Return `(root bases)` with the term's selector root and the selector arguments in traversal order. | Malformed selector. |
| `(l1-structural-measures-selector-hypotheses proof child parent hypotheses)` | Return `(cons scoped hypotheses)` for the selector path from child to parent. The scoped Hypotheses uses the newly derived cons evidence and is `nil` if no scope was found. | Malformed selector or proof construction. |
| `(l1-structural-measures-phase-offsets functions edges)` | Return an alist of phase offsets in first function occurrence order, or `:none` if the requirements have no solution. Each ordered edge is `(caller callee unchanged)`. | Missing function or malformed edge. |
| `(l1-structural-measures-with-phase count phase)` | Return the count term with its integer phase added when nonzero. | None for integer `phase`. |
| `(l1-structural-measures-phase-measures definitions calls)` | Return the first suitable measure assignment in definition order, or the empty alist. Candidate argument positions are visited in ascending order, with the last function varying fastest. | Malformed input, missing function or fuel. |
| `(l1-structural-measures-phased-count term)` | Return `(phase argument)` for a recognized phased count term, or `nil`. | Malformed application. |
| `(l1-structural-measures-phase-decrease proof library goal hypotheses)` | Return `(cons step hypotheses)` for the ordinal comparison goal, with a `nil` Step when the tactic does not apply. Pass `nil` for an absent Hypotheses. | Malformed term or proof construction. |

Any failure replaces the entire result.
