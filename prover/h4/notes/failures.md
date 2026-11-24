# H4 failures

An H4 failure has the form `(:failure kind message)`. Most failures have
kind `"failure"` and an empty message. A caller uses `failure-p` to
recognize either that form or one of the following kinds.

| Kind | Meaning |
|---|---|
| `Fuel` | A recursive computation exhausted its counter. The message names the computation. |
| `Unproved` | A tactic exhausted its proof attempts for the goal. |
| `InapplicableStep` | A required condition for constructing a proof step or applying a tactic was false. |
| `InapplicableTerm` | The tactic could not establish the required term or match it to a supported form. |
| `MissingProofInput` | An arithmetic measure requires a premise absent from the available evidence. |
| `MissingTermPart` | A selector or substitution requires a term component that is absent. |
| `UnusableHint` | A substitution in an instance hint uses a term outside the supported source syntax. |

The kinds tested by the search have empty messages. The consumers below
use the kinds to choose the next proof attempt or to skip an obligation.

| Consumer | Kinds tested and action |
|---|---|
| `h4-book-accumulator-reverse-accumulator-proof-try` | `Unproved` advances to the next induction subject. |
| `h4-book-alists-try-plans`, `h4-book-tactics-retry-proof-p` | `Unproved` and `InapplicableStep` allow another search or induction plan. |
| `h4-book-arity-arity-proof`, `h4-book-projections-projection-proof` | `Unproved`, `InapplicableStep`, `InapplicableTerm` and `MissingProofInput` allow a different tactic. |
| `h4-book-equivalence-unproved-p` | `Unproved` selects the next candidate in equivalence rewriting. |
| `h4-book-equivalence-setoid-try` | `Unproved` and `InapplicableStep` leave the setoid goal open. |
| `h4-book-evaluation-closed-proof`, `h4-book-finite-finite-comparison-proof` | `Unproved`, `InapplicableStep` and `InapplicableTerm` leave the goal open. |
| `h4-book-flatten-append-map-proof`, `h4-book-sets-set-proof`, `h4-book-updates-applicable-step` | `InapplicableStep` leaves the goal open. |
| `h4-book-folds-fold-proof`, `h4-book-tactics-solve-linear` | `InapplicableStep` and `InapplicableTerm` leave the goal open. |
| `h4-book-hanoi-hanoi-corollary-with-book-functions`, `h4-book-numeric-measures-result-with-library` | `Unproved`, `InapplicableStep`, `InapplicableTerm` and `MissingProofInput` leave the goal open when the caller permits another attempt. |
| `h4-book-hints-fact-for-use` | `UnusableHint` omits the unusable instance. |
| `h4-book-list-types-member-type-proof-tests` | `InapplicableStep` advances to the next membership induction candidate. |
| `h4-book-measures-plan-error` | `Unproved`, `InapplicableStep`, `InapplicableTerm`, `MissingProofInput` and `MissingTermPart` allow another measure plan when a previous obligation is known. |
| `h4-book-order-selector-order-establish` | `InapplicableTerm` marks the ordinal comparison `Unproved`. |
| `h4-book-order-selector-order-proof` | `Unproved` leaves the ordinal goal open. |
| `h4-book-run-unproved-p` | `Unproved` advances to another witness or produces a skip entry, according to the caller. |

The predicates also recognize specific failure kinds from the shared books
where those kinds select a fallback. See `prover/FAILURES.md` for their
definitions. Batch results use the reason `unproved` for a skipped
obligation and an empty reason for a completed proof.
