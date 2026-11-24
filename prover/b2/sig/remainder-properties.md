# Remainder properties

`library` is a Library as described in `prover/sig/library.md`. Terms, names
and Steps use the forms in `prover/sig/proof.md`.

| Call | Result | Failure |
|---|---|---|
| `(b2-remainder-properties-remainder-theorem library name formula)` | `(cons step library)` with the Step proving `formula` for theorem symbol `name` and the resulting Library. | May return a failure during proof construction. |

`*b2-remainder-properties-remainder-properties*` is the set of theorem
symbols, listed in ascending order of their serialized forms. Its members
are `LINEARIZE-MOD`, `LINEARIZE-REM`, `MOD-TYPE`, `REM-BOUNDS` and
`REM-TYPE`. The individual constants are `*b2-remainder-properties-linear-mod*`,
`*b2-remainder-properties-linear-rem*`, `*b2-remainder-properties-mod-type*`,
`*b2-remainder-properties-rem-type*` and `*b2-remainder-properties-rem-bounds*`.

`*b2-remainder-properties-abs*` is the symbol `COMMON-LISP::ABS`.
A Remainder has the form
`(:b2-remainder-properties-remainder solver known op value q r gap rx ry nonzero expression)`.
The solver is a Types object from `prover/b2/sig/numeric-types.md`. The Library
is the solver's Library. `known` is an insertion-ordered table of
literals to Steps. `value`, `q`, `r`, and `gap` are the remainder term,
quotient term, ratio, and their difference. `rx` and `ry` prove rationality
of the two arguments. `nonzero` proves that the divisor is nonzero, and
`expression` proves the product formula for `value`. Accessors use the
prefix `b2-remainder-properties-remainder-` and the field name, including
`lib` for the Library.

| Call | Result |
|---|---|
| `(b2-remainder-properties-multiplied-equivalence library left right scale known solver)` | `(cons step solver)` with the Step equating the scaled and unscaled equality tests on `left` and `right`. |
| `(b2-remainder-properties-remainder-init library op known)` | Remainder for operation symbol `op`. |
| `(b2-remainder-properties-remainder-type remainder value)` | `(cons step remainder)` with the rationality Step for term `value`. |
| `(b2-remainder-properties-remainder-with-divisor remainder replies)` | `(cons step remainder)` with both divisor cases combined, or a request for the next case. |
| `(b2-remainder-properties-remainder-comparisons remainder reference negative sign)` | `(cons comparisons remainder)` with the two equality Steps comparing the remainder term and `reference` in both directions. `negative` and `sign` give the divisor sign and its Step. |
| `(b2-remainder-properties-remainder-linearize remainder goal)` | `(cons step remainder)` proving the linearization formula `goal`. |
| `(b2-remainder-properties-remainder-remainder-sign remainder divisor-negative divisor-sign gap-negative gap-sign)` | `(cons step remainder)` proving the remainder's sign from divisor and ratio gap sign Steps and their Booleans. |
| `(b2-remainder-properties-remainder-gap-sign remainder negative weak inexact)` | `(cons step remainder)` with a strict sign Step from the weak bound Step `weak` and the Step `inexact` showing that the ratio is not integral. |
| `(b2-remainder-properties-remainder-signs remainder goal)` | `(cons step remainder)` proving the sign formula `goal`. |
| `(b2-remainder-properties-remainder-unit-gap-bound remainder high negative)` | `(cons step remainder)` with the unit gap bound from strict interval Step `high`. Boolean `negative` picks the side of zero. |
| `(b2-remainder-properties-remainder-absolute-bound remainder goal given lower)` | `(cons step remainder)` proving `goal` given Step `given`. Boolean `lower` selects the lower bound. |

These calls can return a failure as their entire result. A paired Remainder
contains the solver and Library after the call. For a divisor case
request, the first field of the result pair is
`(:call negative sign facts)`. Append a reply `(cons step remainder)` to
the ordered reply list using the Remainder in the request pair, and repeat
the call from its original arguments.
