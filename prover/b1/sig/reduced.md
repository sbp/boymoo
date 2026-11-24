# Reduced rational representations

The `lib` argument is a Library with BookProof behavior. Terms and Steps use the representations in `prover/sig/proof.md`. Each formula is the translated prover term for the corresponding theorem.

| Function | Arguments in order | Result |
|---|---|---|
| `b1-reduced-minimum-denominator-bound` | `lib`, rationality Step for a term, integrality and positivity Steps for a multiplier, integrality Step for their product | `(cons step lib)` with the Step proving that the multiplier is at least the denominator and the Library including auxiliary lemmas |
| `b1-reduced-denominator-minus` | `lib`, formula | `(cons step lib)` with the Step proving the denominator formula and the Library including auxiliary lemmas |
| `b1-reduced-numerator-minus` | `lib`, formula | `(cons step lib)` with the Step proving the numerator formula and the Library including auxiliary lemmas |

Each function may return a failure in place of the pair.
