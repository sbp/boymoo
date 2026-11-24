# Floor ranges

A Library and a Step have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. Every function may return a failure as its entire
result. A pair is `(cons value lib)` with the Library after the call.

`*b2-floor-ranges-sign*`, `*b2-floor-ranges-positive*`,
`*b2-floor-ranges-at-zero*` and `*b2-floor-ranges-at-minus-one*` name
`FLOOR-TYPE-1` through `FLOOR-TYPE-4`, respectively.
`*b2-floor-ranges-floor-ranges*` lists those names for membership tests.

| Call | Result |
|---|---|
| `(b2-floor-ranges-floor-below lib q r k qt rt kt bounds)` | Step equating the strict comparisons of quotient `q` and ratio `r` with threshold `k`. `qt` and `kt` prove integrality, `rt` proves rationality, and `bounds` lists the weak and strict bounds on the ratio. |
| `(b2-floor-ranges-floor-point lib q r level qt rt bounds)` | Pair with the Step equating the test for exact quotient `level` with the test for the ratio's unit interval. `q`, `r`, `qt`, `rt` and `bounds` are as in `floor-below`. |
| `(b2-floor-ranges-strictly-positive-integer lib q typed)` | Step equating positivity with the weak lower bound of one for the integer term `q`, with integer Step `typed`. |
| `(b2-floor-ranges-scaled-threshold lib x y k rx ry sign negative)` | Pair with the Step relating the ratio threshold `k` to a comparison on the dividend and divisor terms `x` and `y`. `rx` and `ry` prove their rationality, `sign` proves the strict divisor sign, and Boolean `negative` selects the negative divisor. |
| `(b2-floor-ranges-floor-range-theorem lib name formula)` | Pair with the Step proving the named theorem with the given formula. |
