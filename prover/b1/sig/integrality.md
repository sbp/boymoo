# Integrality of shifts and halves

The `lib` argument is a Library with BookProof behavior. Terms and Steps use the representations in `prover/sig/proof.md`. Each formula is the translated prover term for the corresponding theorem.

| Function | Arguments in order | Result |
|---|---|---|
| `b1-integrality-half-shift` | `lib`, formula | `(cons step lib)` for the integrality equivalence after a shift |
| `b1-integrality-reflected-half` | `lib`, formula | `(cons step lib)` for the integrality equivalence after reflection |
| `b1-integrality-negated-sum-integral` | `lib`, formula | `(cons step lib)` for integrality of a negated sum |
| `b1-integrality-increment-half` | `lib`, formula | `(cons step lib)` for integrality after an increment of two before halving |
| `b1-integrality-half-choice` | `lib`, formula | `(cons step lib)` for the choice of integral half by residue |
| `b1-integrality-half-complement` | `lib`, formula | `(cons step lib)` for the complementary integrality tests |

The Step proves the formula and the Library includes any auxiliary lemmas. Each function may return a failure in place of the pair. The constants `*b1-integrality-two*` and `*b1-integrality-half*` are quoted prover terms.
