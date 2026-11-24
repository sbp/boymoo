# Positive cofactors

`proof` is the H1 Prover and `norm` is the Algebra object from
`book-arithmetic`. Terms and Steps have the forms in `prover/sig/proof.md`.
`call` is a Call in the form in `prover/sig/termination.md`. The prover
symbols are `*h1-book-cofactors-cofactors*`, `*h1-book-cofactors-posp*`
and `*h1-book-cofactors-lambda*`.

| Call | Result |
|---|---|
| `(h1-book-cofactors-combine terms)` | The right-associated conjunction of the terms in their given order. |
| `(h1-book-cofactors-components proof statement)` | List of the component Steps of the conjunction Step `statement`, from left to right. |
| `(h1-book-cofactors-tuple-of g a b)` | The term constructing the ordered triple with components `g`, `a` and `b`. |
| `(h1-book-cofactors-tuple-terms value)` | Three terms projecting the components of `value` in tuple order. |
| `(h1-book-cofactors-positive-parts proof statement)` | Two Steps proving integrality and strict positivity from the `POSP` Step `statement`. |
| `(h1-book-cofactors-positive-integer proof term integral sign)` | The `POSP` Step for `term` from its integer and strict sign Steps. |
| `(h1-book-cofactors-measure-of a b)` | The measure term for the arguments `a` and `b`. |
| `(h1-book-cofactors-natural-measure proof a b)` | The Step proving the measure natural. |
| `(h1-book-cofactors-measure-value proof args evidence)` | The Step opening the measure of the two argument terms using their `POSP` Steps in argument order. |
| `(h1-book-cofactors-positive-difference proof norm smaller greater bound)` | `(cons step norm)` with a positivity Step for the difference of the terms and the Algebra after normalization. `bound` is a strict comparison Step. |
| `(h1-book-cofactors-positive-pair proof norm)` | `(cons steps norm)` with the two `POSP` Steps for `X` and `Y` and the Algebra after recording their integer and sign evidence in order. |
| `(h1-book-cofactors-child-positive proof norm args pair)` | `(cons (list index steps) norm)` with the zero-based position of the changed argument in `args`, the updated `POSP` list and the resulting Algebra. `pair` contains the parent arguments' `POSP` Steps. |
| `(h1-book-cofactors-descent-proof proof call)` | The measure-decrease Step for the recursive call. |
| `(h1-book-cofactors-define-cofactors proof)` | `(cons (list ordinal descents) proof)` with the ordinality Step, the list of `(call decrease-step)` pairs in source order and the Prover with the definition and measure entries. |
| `(h1-book-cofactors-aligned-integer proof norm expression evidence)` | `(cons step norm)` with the Step transferring `evidence` to `expression` across a normalized identity and the updated Algebra. |
| `(h1-book-cofactors-equal-from-bounds proof norm)` | `(cons step norm)` with the equality Step for `Y` and `X` under their weak bounds and the updated Algebra. |
| `(h1-book-cofactors-cofactors-spec result)` | The six specification literals on the three components of `result` in theorem order. |
| `(h1-book-cofactors-expose-tuple-fact proof opened literals evidence)` | The list of Steps rewritten to the given `literals` in order. `opened` equates the result to a constructed triple, and `evidence` is the list of component Steps before rewriting. |
| `(h1-book-cofactors-prove-cofactor-spec proof ordinal descents)` | The updated Prover with the positive cofactors theorem. The two proof arguments are the values from `define-cofactors`. |
| `(h1-book-cofactors-install-cofactors proof)` | The Prover with the cofactor definition, its measure and its specification. |

`combine` returns a failure for an empty term list. Calls that construct
Steps or extend a prover can return a failure. The terms, Steps, and
pairs in each list retain their order of construction.
