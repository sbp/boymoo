# Countdown proof signatures

`lib` is a library, `step` is a proof step and `rulers` is a `Rulers` object. `goal` is a strict ordinal comparison. A nil step denotes that the tactic did not find a proof. A returned library includes all definitions and lemmas added by the call, including calls with a nil step. All functions can return a failure in place of their result.

`*countdowns-counter-wrappers*` is the ordered list of the three wrapper names, each in the representation returned by `proof-sym`.

| ACL2 call | Arguments and result |
|---|---|
| `(countdowns-nfix-ordinal lib measure)` | `measure` is a term. Returns `(cons step lib)` with an ordinality proof for an `NFIX` application, or a nil step. |
| `(countdowns-negate-sum-lemma lib)` | Adds distribution of unary minus across a sum and returns the resulting library. |
| `(countdowns-unit-shift lib after before unit)` | `after` and `before` are terms and `unit` is the integer offset. Returns `(cons step lib)` with the equality of `after` and `before` plus the offset, or a nil step. |
| `(countdowns-nfix-step-lemma lib)` | Adds the strict decrease of `NFIX` after a unit subtraction and returns the resulting library. |
| `(countdowns-positive-gap lib value evidence rulers)` | `value` is a term and `evidence` is a list of proof steps. Returns `(cons step lib)` with a proof that `value` is positive, or a nil step. |
| `(countdowns-clip-naturals lib term)` | `term` is a counter term. Returns `(cons step lib)` with an equality that removes clipping around natural summands, or a nil step. |
| `(countdowns-counter-shift lib child parent)` | `child` and `parent` are counter terms. Returns `(cons step lib)` with a unit decrease equality, or a nil step. |

`(countdowns-wrapped-countdown-with-rulers lib goal rulers)` and `(countdowns-clipped-decrease-with-rulers lib goal rulers)` return `(cons (list step rulers) lib)` or a failure. The returned Rulers holds the evidence established during the queries.
