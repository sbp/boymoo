# Floor sums and remainders

The `lib` argument is a Library with BookProof behavior. Terms and Steps use the representations in `prover/sig/proof.md`. Each formula is the translated prover term for the corresponding theorem.

| Function | Arguments in order | Result |
|---|---|---|
| `b1-floor-sum-floor-sum` | `lib`, the floor sum formula | `(cons step lib)` with the Step proving the formula and the Library including auxiliary lemmas |
| `b1-floor-sum-mod-sum` | `lib`, the remainder sum formula | `(cons step lib)` with the Step proving the formula and the Library including auxiliary lemmas |

Each function may return a failure in place of the pair. `*b1-floor-sum-floor-sum*` is the prover symbol for `(floor (+ x y) z)`.

A FloorSum has tag `:b1-floor-sum` and, in order, fields for the first term, second term, divisor, numerator, inverse, quotients before flooring, floors, remainders, sum of quotients, sum of floors, sum of remainders, successor of the floor sum, carry test and rational evidence. The Library and the NumberSums using it are carried alongside this record so that proofs preserve changes to the shared Library. The two-element lists of quotients, floors and remainders are in addend order.

`(b1-floor-sum-floor-sum-init lib first second divisor rationals)` returns the FloorSum or a failure. Its final field is the NumberSums object holding the Library. `(b1-floor-sum-floor-sum-lib work)` returns that Library. `(b1-floor-sum-floor-sum-with-lib work lib)` returns the FloorSum with the supplied Library in its NumberSums. The last two calls return their results directly.
