# Association lookup proofs

`lib` is the tactic library. Terms and Steps use the forms in `prover/sig/proof.md`. Each call returns a Step or a failure, with the callback request described below as an intermediate result of `lookup-property`.

| Call | Arguments and result |
|---|---|
| `(b2-association-lookup-property lib formula lookup source source-calls base-calls entry-evidence)` | Induction proof of `formula` using the association application `lookup` and the source predicate application `source`. `source-calls` and `base-calls` are lists of terms or names to unfold in the entry and base cases, respectively. Pass `nil` for either empty list. |
| `(b2-association-enabled-runep lib formula)` | Proof of the enabled-rune property in `formula`. |
| `(b2-association-pseudo-term-of-assoc lib formula)` | Proof that the selected association contains a pseudo-term. |
| `(b2-association-symbol-dereference lib formula)` | Proof that dereferencing a symbol gives a symbol. |

Use `nil` for `entry-evidence` when the induction needs only its supplied evidence. Pass `:request` to obtain `(:b2-association-entry-evidence records per-entry)` or a failure. Prove the additional evidence with `lib`, the association-list term `records`, and the Step `per-entry`. Then call again with `(:reply evidence)` as the last argument. `evidence` is the ordered list of additional Steps or a failure. The request occurs during the induction step, before either lookup branch.

The symbol constants are `*b2-association-assoc*`, `*b2-association-assoc-cdr*`, `*b2-association-strip*`, `*b2-association-pseudo-term*` and `*b2-association-r-symbol-alist*`.
