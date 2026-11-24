# Shift arithmetic

`*shift-arithmetic-ash*`, `*shift-arithmetic-expt*`,
`*shift-arithmetic-fix*` and `*shift-arithmetic-zip*` are prover symbols.
`*shift-arithmetic-two*` is the term quoting 2.

The `lib` argument is a Library. A term and a Step have the forms in
`prover/sig/proof.md`. The `rulers` argument is a Rulers object as described in
`prover/sig/rulers.md`. Every function can return a failure in place of its
listed result.

| ACL2 call | Arguments and result |
|---|---|
| `(shift-arithmetic-inverse-power lib shifts)` | The integer number of shifts. Returns the Step evaluating the corresponding negative power of two. |
| `(shift-arithmetic-unscaled-floor lib term integral shifts radix)` | The shift term, the dividend's integer Step, the number of shifts and the literal radix term. Returns the equality Step between the shift and floor by the radix. |
| `(shift-arithmetic-shift-decrease lib goal rulers)` | A count comparison term and its Rulers. Returns `(step . lib)` with the resulting Library. The Step is `nil` when the shift does not establish descent. |

`(shift-arithmetic-shift-decrease-with-rulers lib goal rulers)` returns
`((step rulers) . lib)` with the Rulers after its hypothesis queries.
The Step is optional. A failure can appear in place of the pair.
