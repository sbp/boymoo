# Truncation intervals

A Library and a Step have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. Every function may return a failure as its entire
result. A pair is `(cons value lib)` with the Library after the call.

`*b2-truncate-intervals-truncate-bounds*` is the theorem name `TRUNCATE-BOUNDS`.

| Call | Result |
|---|---|
| `(b2-truncate-intervals-positive-ratio-scale lib x y rx ry sign negative)` | Pair whose value is `(ratio scale ratio-type scale-type positive reduced)`. `x` and `y` are dividend and divisor terms, `rx` and `ry` prove their rationality, and `sign` proves the strict sign of the divisor. Boolean `negative` is true for a negative divisor. The result gives the ratio, the absolute value of the divisor, their rationality Steps, the scale's positivity Step, and the equality Step reducing the scaled ratio. |
| `(b2-truncate-intervals-zero-scaled-comparisons lib ratio scale ratio-type scale-type positive reduced)` | Pair with the list of two equality Steps for the comparison of `ratio` with zero and of zero with `ratio`, respectively. The terms and Steps are as returned by `positive-ratio-scale`. |
| `(b2-truncate-intervals-ratio-comparisons lib x y rx ry sign negative)` | Pair with the list of two equality Steps relating ratio signs to dividend signs. The first equality compares the ratio with zero after scaling, and the second compares zero with the ratio after scaling. The arguments are as in `positive-ratio-scale`. |
| `(b2-truncate-intervals-truncate-interval lib x y rx ry sign negative)` | Pair with the list of the weak and strict truncation bound Steps, in that order. `sign` proves that the ratio is nonnegative or nonpositive. Boolean `negative` selects the nonpositive branch. The other arguments are as in `positive-ratio-scale`. |
| `(b2-truncate-intervals-add-unit-at-right lib inequality quotient-type)` | Shifted inequality Step, given the strict bound Step and an integer Step for its quotient. |
| `(b2-truncate-intervals-truncation-bounds lib formula)` | Pair with the Step proving the four branches of the signed bounds formula. |
