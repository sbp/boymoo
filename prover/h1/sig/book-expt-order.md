# Order of powers

`proof` is the H1 prover. Terms and Steps have their forms in `prover/sig/proof.md`. `normalizer` is the field normalizer of `prover/h1/sig/book-field.md`.

| Function | Arguments in order | Result |
|---|---|---|
| `h1-book-expt-order-install-transitivity` | `proof` | Updated prover with rational transitivity. |
| `h1-book-expt-order-positive-base` | `proof`, base term, `normalizer` | `(cons step normalizer)` with a proof that the base is positive. |
| `h1-book-expt-order-scale` | `proof`, strict comparison Step, multiplier term, positivity Step, `normalizer` | `(cons step normalizer)` with the scaled comparison. |
| `h1-book-expt-order-install-positive-power` | `proof` | Updated prover with the positive power lemma. |
| `h1-book-expt-order-install-power-above-one` | `proof` | Updated prover with the power above one lemma. |
| `h1-book-expt-order-install-power-order` | `proof` | Updated prover with the rational power rule and the three lemmas. |
| `h1-book-expt-order-power-monotonicity` | `proof`, implication or strict comparison term | Step for the formula. |

Every function can return a failure as its entire result. `power-monotonicity` can return `unproved` when the formula does not match or lacks the necessary evidence.

`(h1-book-expt-order-step-term step index)` reads a zero-based index of the first literal of a Step. `(h1-book-expt-order-bindings pairs bindings)` extends the given dictionary with the two-element binding pairs in order. Either helper can return a failure when reading its input.
