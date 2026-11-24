# Finite interval case analysis

The `p` argument is a Tactics Library as specified in `prover/h4/sig/tactics.md`. Terms and Steps have the forms in `prover/sig/proof.md`. A domain is a list of consecutive integers in increasing order, and argument variables are in call order. An exclusion list has one Step for each point, in increasing order.

| Call | Result |
|---|---|
| `(h4-book-finite-constructor-test p)` | An equality Step for the value of CONSP of a CONS expression, in the variables `X` and `Y`. |
| `(h4-book-finite-reduction-provider p)` | A provider for CAR, CDR, and CONSP over CONS expressions, to pass directly to normalization or establishment. |
| `(h4-book-finite-reduction-provider-provide term p consp-cons)` | The Step for a provider call on `term`, using the `consp-cons` Step from `constructor-test`, or `nil`. |
| `(h4-book-finite-proposition-from-interval p term start end integral lower upper excluded)` | A contradiction Step from the inclusive interval bounds `start` and `end`, their evidence Steps `lower` and `upper`, the integrality Step `integral`, and the exclusion Steps `excluded`. |
| `(h4-book-finite-finite-interval-shape formula)` | `(arguments domain)` for a matching formula, or `nil`. |
| `(h4-book-finite-prove-interval-cases p formula arguments domain)` | A Step proving `formula` by case analysis on the given variables and domain. |
| `(h4-book-finite-finite-comparison-proof p formula)` | The finite comparison Step for a matching formula, or `nil` if the shape or proof fails. |

Each call can return a failure as its entire result. The last call returns `nil` for the interval proof fallback kinds in `prover/h4/notes/failures.md`.
