# H4 failures

An H4 failure has the form `(:failure kind message)`. Most failures have
kind `"failure"` and an empty message. A caller uses `failure-p` to
recognize either that form or one of the following kinds.

| Kind | Meaning |
|---|---|
| `fuel` | A recursive computation exhausted its counter. The message names the computation. |
| `unproved` | A tactic exhausted its proof attempts for the goal. |
| `inapplicable-step` | A required condition for constructing a proof step or applying a tactic was false. |
| `inapplicable-term` | The tactic could not establish the required term or match it to a supported form. |
| `missing-proof-input` | An arithmetic measure requires a premise absent from the available evidence. |
| `missing-term-part` | A selector or substitution requires a term component that is absent. |
| `unusable-hint` | A substitution in an instance hint uses a term outside the supported source syntax. |

The kinds tested by the search have empty messages. The consumers below
use the kinds to choose the next proof attempt or to skip an obligation.

| Consumer | Kinds tested and action |
|---|---|
| `h4-book-accumulator-reverse-accumulator-proof-try` | `unproved` advances to the next induction subject. |
| `h4-book-alists-try-plans`, `h4-book-tactics-retry-proof-p` | `unproved` and `inapplicable-step` allow another search or induction plan. |
| `h4-book-arity-arity-proof`, `h4-book-projections-projection-proof` | `unproved`, `inapplicable-step`, `inapplicable-term` and `missing-proof-input` allow a different tactic. |
| `h4-book-equivalence-unproved-p` | `unproved` selects the next candidate in equivalence rewriting. |
| `h4-book-equivalence-setoid-try` | `unproved` and `inapplicable-step` leave the setoid goal open. |
| `h4-book-evaluation-closed-proof`, `h4-book-finite-finite-comparison-proof` | `unproved`, `inapplicable-step` and `inapplicable-term` leave the goal open. |
| `h4-book-flatten-append-map-proof`, `h4-book-sets-set-proof`, `h4-book-updates-applicable-step` | `inapplicable-step` leaves the goal open. |
| `h4-book-folds-fold-proof`, `h4-book-tactics-solve-linear` | `inapplicable-step` and `inapplicable-term` leave the goal open. |
| `h4-book-hanoi-hanoi-corollary-with-book-functions`, `h4-book-numeric-measures-result-with-library` | `unproved`, `inapplicable-step`, `inapplicable-term` and `missing-proof-input` leave the goal open when the caller permits another attempt. |
| `h4-book-hints-fact-for-use` | `unusable-hint` omits the unusable instance. |
| `h4-book-list-types-member-type-proof-tests` | `inapplicable-step` advances to the next membership induction candidate. |
| `h4-book-measures-plan-error` | `unproved`, `inapplicable-step`, `inapplicable-term`, `missing-proof-input` and `missing-term-part` allow another measure plan when a previous obligation is known. |
| `h4-book-order-selector-order-establish` | `inapplicable-term` marks the ordinal comparison `unproved`. |
| `h4-book-order-selector-order-proof` | `unproved` leaves the ordinal goal open. |
| `h4-book-run-unproved-p` | `unproved` advances to another witness or produces a skip entry, according to the caller. |

The predicates also recognize specific failure kinds from the shared books
where those kinds select a fallback. See `prover/FAILURES.md` for their
definitions. Batch results use the reason `unproved` for a skipped
obligation and an empty reason for a completed proof.
