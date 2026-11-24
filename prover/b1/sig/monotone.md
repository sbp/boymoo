# Exponentiation with a rational base above one

`lib` is a Library. `base`, `exponent`, and `formula` are terms. `rational`
and `base-bound` are Steps proving the base rational and strictly above 1.
`integral` and `natural` are Steps giving the indicated type of the exponent.
Terms and Steps have the forms in `prover/sig/proof.md`.

| Call | Result |
|---|---|
| `(b1-monotone-rational-expt lib base exponent rational)` | Step proving the power rational. |
| `(b1-monotone-natural-power-bound lib)` | `(cons name lib)` with the fact name for the bound on powers with natural exponents. |
| `(b1-monotone-bound-for-power lib base exponent natural rational base-bound)` | `(cons step lib)` instantiating the natural exponent bound for the given terms and Steps. |
| `(b1-monotone-positive-power lib base integral rational base-bound)` | `(cons step lib)` proving that the power with the given integer exponent is positive. |
| `(b1-monotone-increasing-power lib formula)` | `(cons step lib)` proving the monotonicity implication `formula`. |

In each pair, `lib` is the resulting Library. Each call may return a failure
as its entire result. The natural exponent induction has one substitution
binding the exponent to its predecessor.
