# Failures in B2

B2 uses the failure values described in `prover/FAILURES.md`. `fuel` names
the recursion that exhausted its counter. `unproved` has an empty message
and lets the search continue at call sites that have another proof method.
An operation that has no way to continue returns or propagates a failure.

| Kind | Meaning | Tests |
|---|---|---|
| `inapplicable` | The formula, evidence, or candidate does not satisfy the conditions of a proof method. | `b2-search-rejected-step-p` lets search move to another inference. `b2-measures-rejected-step-p` lets measure proofs try another argument or measure. `b2-next-recipes-prove-new-theorem-type` falls back from type propagation to search. `b2-api-claim-attempts` moves to the next theorem tactic. |
| `tactic-rejected` | A theorem tactic encounters a shape it cannot use, a missing prerequisite, or a failed proof condition. | `b2-api-claim-attempts` moves to the next theorem tactic. |

Both kinds have empty messages. Calls to shared books can propagate their
failure values. `b2-bounds-unusable-bound-p` and the search fallbacks also
recognize the shared `value` kind. The theorem dispatcher recognizes the
shared kinds that let it try another tactic.

`grep -nE 'inapplicable|tactic-rejected|b2-tactics-unproved-p' prover/b2/*.lisp`
shows the producers and consumers. The command was run on 2026-11-23.
