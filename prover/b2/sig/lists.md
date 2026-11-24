# List induction proofs

`lib` is the tactic library. Terms and Steps use the forms in `prover/sig/proof.md`. Evidence and unfold arguments are ordered lists. Each call may return a failure in place of the listed result.

| Call | Arguments and result |
|---|---|
| `(b2-lists-open-literal lib literal step evidence unfold)` | Normalize the term `literal` with `evidence` and `unfold`, then apply the resulting equation to `step` and tidy the result. |
| `(b2-lists-opened-conjuncts lib step evidence unfold)` | Two Steps for the conjuncts of the normalized first literal of `step`. |
| `(b2-lists-rational-sum lib formula)` | Proof of the rational sum implication `formula`. |
| `(b2-lists-sum-append lib formula)` | Proof of the sum and append equality `formula`. |
| `(b2-lists-mapped-recognizer lib formula)` | Proof of the recognizer application `formula` for one of the list mappings. |

The symbol constants are `*b2-lists-map-names*`, `*b2-lists-char-list*`, `*b2-lists-make-chars*` and `*b2-lists-fix*`.
