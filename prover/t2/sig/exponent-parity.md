# Exponent parity

Terms, Steps and the Library use the forms in `prover/sig/proof.md` and
`prover/sig/library.md`. A flag `forward` is `t` for a positive exponent and
`nil` for a negative exponent.

`*t2-exponent-parity-half*` is quoted `1/2`. `*t2-exponent-parity-evenp*`
and `*t2-exponent-parity-oddp*` are the Common Lisp symbols `EVENP` and `ODDP`.

| Call | Result | Failure |
|---|---|---|
| `(t2-exponent-parity-half-integral exponent)` | The integer test for half of the exponent term. | None. |
| `(t2-exponent-parity-parity-step lib shift)` | A Step for translation of the half-integer test by the integer `shift`. | A failure from proof construction. |
| `(t2-exponent-parity-countdown-step lib integral sign forward)` | `(cons (list smaller step) lib)` with the exponent one step nearer zero, its ordinal-decrease Step, and the resulting Library. `integral` and `sign` are Steps for the original exponent. The negative direction can add lemmas. | A failure from proof construction. |
| `(t2-exponent-parity-build lib)` | The Library with the exponent parity lemmas in recipe order. | A failure from proof construction. |

All other non-lifted calls in the table below take the Library first and can return a
failure from proof construction. In `values`, the dictionary of constant powers
maps each exponent integer to its Step in the insertion order `0, 1, 2, -1, -2`.

| Call | Result |
|---|---|
| `(t2-exponent-parity-integer-translation lib)` | Library with the integer-translation test. |
| `(t2-exponent-parity-parity-predicates lib)` | Library with the two predicate definitions as half-integer tests. |
| `(t2-exponent-parity-two-step lib integral forward)` | `(cons (list shifted step) lib)` for the exponent two steps nearer zero and its ordinal decrease. `integral` proves the exponent `Y` integral. |
| `(t2-exponent-parity-minus-one-constants lib)` | `(list values numeric nonzero)`, where `numeric` and `nonzero` prove those properties of the base `-1`. |
| `(t2-exponent-parity-integer-equality lib a b integer-facts weak-ab weak-ba)` | Equality Step for terms `a` and `b`, from integer evidence and the two weak bounds. |
| `(t2-exponent-parity-near-zero-at index equality lib values)` | Step for the parity formula at integer `index`, transported by the Step `equality` to the exponent `Y`. |
| `(t2-exponent-parity-near-zero lib iy values)` | Step for the parity formula at the three exponents nearest zero. `iy` is the integer Step for `Y`. |
| `(t2-exponent-parity-power-minus-one lib)` | Library with the formula for powers of `-1`. |
| `(t2-exponent-parity-negative-base lib)` | Library with the even and odd rewrites and sign lemmas for negative bases. |
| `(t2-exponent-parity-integral-exponent-test lib)` | Library with the test for when an integer base above one has an integral power. |

The lifted `near-zero-at` function takes its captured `lib` and `values`
after `index` and `equality`, as shown in the table.
