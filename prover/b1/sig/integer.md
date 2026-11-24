# Integer bounds and clipped measures

`library` is a Library as defined in `prover/sig/library.md`. Terms and Steps
use the forms in `prover/sig/proof.md`. Each function returns a Step or a failure.

| ACL2 function and arguments | Result |
|---|---|
| `(b1-integer-open-unit-interval library formula)` | Step proving the implication `formula` excluding integers strictly between zero and one. |
| `(b1-integer-nfix-equation library argument)` | Step equating ACL2's `NFIX` on term `argument` with `SELF-NFIX` on the same term. |
| `(b1-integer-nfix-natural library term)` | Step proving the `NFIX` call `term` natural. |
| `(b1-integer-nfix-identity library natural)` | Step equating `NFIX` on the term in the naturality Step `natural` with that term. |
| `(b1-integer-no-zp library term negative integer)` | Step proving `term` positive from a negative `ZP` Step and an integrality Step. |
| `(b1-integer-clipped-ordinal library measure)` | Step proving the `NFIX` measure term an ordinal. |
| `(b1-integer-clipped-advance library goal hypotheses)` | Step proving the clipped gap decreases in the ordinal comparison `goal`. Pass the Hypotheses object described in `prover/sig/descent.md`, using the signed tests in their original order. |
| `(b1-integer-successor-is-larger library x)` | Step proving that term `x` is strictly below one plus `x`. |

`*b1-integer-nfix*` is the symbol term for `ACL2::NFIX`.
