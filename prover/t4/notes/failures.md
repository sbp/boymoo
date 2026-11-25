# Failures in T4

A failure is `(:failure kind message)`. The generic kind is `"failure"`
with an empty message. `"fuel"` carries the name of the recursion that
exhausted its counter. All other T4 failure messages are empty.

| Kind | Meaning | Tests |
|---|---|---|
| `"unproved"` | Generation exhausted its measure candidates or could not construct the requested witness. | `t4-slice-unproved-p`, `t4-slice-measure-case-step` and `t4-slice-try-measures` handle unsuccessful generation. `t4-bookrun-book-entry` selects the witness fallback or marks the entry as skipped. `t4-evaluator-witness-validated`, `t4-bookwitness-trial-failure-p` and `t4-ordered-retry-comparison-p` also recognize it. |
| `"search-miss"` | A search candidate could not produce the required evidence or a proof within its search budget. | `t4-algebra-search-miss-p`, `t4-booklogic-search-miss-p`, `t4-booklogic-search-failure-p`, `t4-list-types-search-miss-p`, `t4-ordered-retry-comparison-p`, `t4-slice-measure-case-step`, `t4-slice-try-measures`, `t4-bookrun-book-entry`, `t4-evaluator-witness-validated` and `t4-bookwitness-trial-failure-p`. |
| `"inference-mismatch"` | A candidate's terms, hypotheses or conclusion do not satisfy the inference's conditions. | `t4-booklogic-search-failure-p`, `t4-slice-try-measures`, `t4-bookrun-book-entry`, `t4-evaluator-witness-validated` and `t4-bookwitness-trial-failure-p`. |
| `"missing-proof-input"` | A measure, definition or other input required by a proof recipe is absent. | `t4-slice-try-measures`, `t4-bookrun-book-entry` and `t4-evaluator-witness-validated`. |
| `"malformed-candidate"` | The terms of an evaluator witness candidate or its measure lack the required shape. | `t4-evaluator-witness-validated` lets the witness search try another method. |
| `"MissingProof"` | A supplied reply reports an unavailable proof. | `t4-ordered-retry-comparison-p` and `t4-bookwitness-trial-failure-p` accept this kind in replies. |

Search branches that receive failures from shared books also recognize the
kinds described in `prover/FAILURES.md`.
