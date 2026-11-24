# T2 book responsibilities

| Responsibility | Books |
|---|---|
| Naming and rewriting helper entries | `api-names`, `rename` |
| Proof context, obligations, and the public interface | `books`, `api-engine`, `api`, `open` |
| Ordered rule search and hints | `book-logic`, `hints` |
| Termination, selector bounds, and list measures | `tactics`, `guarded-selectors`, `lists`, `countdown`, `phase` |
| Arithmetic normalization and order | `arithmetic`, `products`, `field`, `field-cancellation`, `order`, `subtraction` |
| Division, rounding, and discrete bounds | `quotient`, `floor`, `half`, `floor-split`, `quotient-rounding`, `rounding`, `round-ties`, `floor-bracket`, `floor-thresholds`, `half-parity` |
| Powers, rationals, and numeric types | `power`, `power-products`, `power-transport`, `exponent-parity`, `exponent-equalities`, `ratios`, `rational-scaling`, `numeric-types`, `dyadic`, `completed-operations` |
| Conditional and multiplicative proofs | `conditional`, `euclid`, `factorization` |
| Constraint witnesses | `evaluator`, `equational-witness` |
| State and input channel invariants | `input-fields`, `input-state`, `input-channels` |
| Structural proofs and tree invariants | `structural-proof`, `structural-lists`, `symbol-trees`, `tree-rebalance` |

`prover/t2/ORDER` gives the certification order. Calls can use definitions
in the shared books through `descent` and in T2 books earlier in that order.
