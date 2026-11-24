# Positive integer modulus

`lib` is a Library. Terms and Steps have the forms in `prover/sig/proof.md`.
`*b1-modular-mod*` is the `COMMON-LISP` symbol term `MOD`.

A Modulus has the form `(:b1-modulus lib integer positive divisor)`.
`integer` and `positive` are the Steps supplied on construction, and
`divisor` is the argument of the first literal of `integer`. Use the
constructor and accessors below. A return of `(cons value lib)` carries the
current Library. A Modulus used with that Library can be updated using
`b1-modular-modulus-with-lib`.

| Call | Result | Failure |
|---|---|---|
| `(b1-modular-modulus-init lib integral strict)` | Modulus for the divisor proved integer by `integral` and positive by `strict`. | From reading the Step or its first literal. |
| `(b1-modular-modulus-lib ring)` | The Modulus's Library. | None. |
| `(b1-modular-modulus-integer ring)` | Its integer Step. | None. |
| `(b1-modular-modulus-positive ring)` | Its positivity Step. | None. |
| `(b1-modular-modulus-divisor ring)` | Its divisor term. | None. |
| `(b1-modular-modulus-with-lib ring lib)` | The Modulus with the supplied Library. | None. |
| `(b1-modular-modulus-mod ring argument)` | Modulus term for `argument` and the divisor. | None. |
| `(b1-modular-modulus-floor ring argument)` | Floor term for `argument` and the divisor. | None. |
| `(b1-modular-modulus-ratio ring argument)` | Product of `argument` and the reciprocal of the divisor. | None. |
| `(b1-modular-modulus-rational ring argument integral)` | Step proving the ratio rational, using the integer Step `integral` for `argument`. | From proof construction. |
| `(b1-modular-modulus-inverse ring reverse)` | Step proving the product of the divisor and its reciprocal is 1. Boolean `reverse` selects the reciprocal as the first factor when true. Pass `nil` for the default. | From proof construction. |
| `(b1-modular-modulus-inverse-positive ring)` | `(cons step lib)` proving the reciprocal positive. | From proof construction. |
| `(b1-modular-modulus-scale-ratio ring term integral)` | Step reducing the divisor times the ratio of `term` to `term`, using its integer Step `integral`. | From proof construction. |
| `(b1-modular-modulus-bounds ring integral)` | `(cons steps lib)` with the integer, nonnegative, and strict upper bound Steps for the remainder of the term from `integral`, in that order. | From proof construction. |
| `(b1-modular-modulus-canonical ring integral lower upper)` | `(cons step lib)` proving the remainder of the term from `integral` is that term, given its nonnegative Step `lower` and strict upper bound Step `upper`. | From proof construction. |
| `(b1-modular-modulus-product ring first second left)` | `(cons step lib)` proving that the factor from integer Step `first` can be replaced by its residue in the product with the factor from integer Step `second`, inside the modulus. Boolean `left` selects the first position when true. Pass `t` for the default. | From proof construction. |
| `(b1-modular-modulus-product-congruence ring first second fixed equality left)` | `(cons step lib)` lifting residue `equality` for the terms of integer Steps `first` and `second` through a product with the term of integer Step `fixed`. Boolean `left` selects the first position when true. Pass `t` for the default. | From proof construction. |

| Call | Result | Failure |
|---|---|---|
| `(b1-modular-remainder-lemma lib)` | `(cons name lib)` with the remainder interval fact name. | From proof construction. |
| `(b1-modular-remainder-consequence lib formula)` | `(cons step lib)` proving the integer type or a bound selected by `formula`, for a constant positive divisor. | A failure if no bound or type matches or the proof cannot be constructed. |
| `(b1-modular-exact-remainder-quotient lib formula)` | `(cons step lib)` proving the known-remainder quotient equation `formula`. | From proof construction or unpacking the formula. |
| `(b1-modular-exact-remainder-integral lib formula equality)` | `(cons step lib)` proving the integer type in `formula`. `equality` is the quotient equation's fact name string, or `:none` to look up the equation by its claim. | A failure if no equation matches or the proof cannot be constructed. |
| `(b1-modular-shift-lemma lib)` | `(cons name lib)` with the integer shift fact name. | From proof construction. |
| `(b1-modular-product-lemma lib)` | `(cons name lib)` with the factor reduction fact name. | From proof construction. |

In each pair, `lib` is the resulting Library. Any failure is the entire
result. Fact bindings and the remainder bounds retain their source order.

`(b1-modular-exact-remainder-integral-with-claims lib formula equality claims)`
takes the same arguments followed by the claims table accepted by
`b1-logic-matching-claim`. Supply that table when `equality` is `:none` and
the statement context has an index. The three-argument entry point uses an
empty claims table. The result and failure conditions are the same for both calls.
