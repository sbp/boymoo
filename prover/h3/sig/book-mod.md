# Remainder proofs

A Library, Step and term have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. A Bounds object has the form in
`prover/h3/sig/book-order.md`. A `call` is a two-argument remainder term,
except where a floor term is specified. Evidence read from Bounds follows
insertion order.

`*h3-book-mod-mod*` is the term symbol for `COMMON-LISP::MOD`.
`*h3-book-mod-mod-positive-bounds*` is the list of applicable theorem
name strings in ascending string order. The tactic tests membership.

| Call | Arguments and result |
|---|---|
| `(h3-book-mod-mod-floor-zero library call product-zero x-numeric)` | Remainder term, Step that the subtracted product is zero, and numeric type Step for the dividend or `nil`. Returns the Step evaluating the remainder. |
| `(h3-book-mod-mod-zero-divisor library call zero x-numeric)` | Remainder term, Step that the divisor is zero or `nil`, and numeric type Step for the dividend or `nil`. Returns the Step evaluating the remainder. |
| `(h3-book-mod-mod-zero-dividend library call missing)` | Remainder term and Step that the dividend is nonnumeric, or `nil` for literal zero. Returns the Step evaluating the remainder. |
| `(h3-book-mod-mod-using-fl library call)` | Remainder term. Returns the Step rewriting its definition using `FL`. |
| `(h3-book-mod-remainder-reconstruction library call numeric)` | Remainder term and numeric type Step for the dividend. Returns `(cons step library)` with the reconstruction equality. |
| `(h3-book-mod-add-back library call opened part numeric)` | Remainder term, Step unfolding it, quotient product term and numeric type Step for the dividend. Returns `(cons step library)` with the equality that adds the product back. |
| `(h3-book-mod-mod-exact-if-integer-ratio library call i-numeric j-numeric notzero ratio-integer)` | Remainder term, numeric type Steps for both arguments, and Steps that the divisor is nonzero and the ratio is an integer. Returns the Step for zero remainder. |
| `(h3-book-mod-floor-zero-with-mixed-types library call rational nonrational)` | Two-argument floor term and Steps that one argument is rational and the other is nonrational. Returns the Step for a zero floor. |
| `(h3-book-mod-remainder-rational library call i-rational j-rational)` | Remainder term and rationality Steps for its arguments. Pass `nil` for omitted `j-rational`. Returns `(cons step library)` with the rationality Step for the remainder. |
| `(h3-book-mod-positive-noncomplex-is-rational library term positive noncomplex)` | Term and Steps for positivity and noncomplexity. Returns its rationality Step. |
| `(h3-book-mod-remainder-bounds library call i-type j-type order direction)` | Remainder term, rationality Steps for both arguments, Step for the divisor's sign, and integer direction. Returns `(cons bounds library)`. With a negative direction, `bounds` is the one-element list of the nonpositive Step. Otherwise it is the list of the lower and upper Steps, in that order. |
| `(h3-book-mod-mod-noncomplex-bounds library call context)` | Remainder term and Bounds. Returns `(cons (list lower upper rational divisor-type) library)`. |
| `(h3-book-mod-mod-bound-goal library goal context call)` | Goal term, Bounds and remainder term. Returns `(cons step library)` with the proof of the bound or conjunction of bounds. |
| `(h3-book-mod-mod-type-equivalence library goal context)` | Goal term and Bounds. Returns `(cons step library)` with the proof of type equivalence. |
| `(h3-book-mod-mod-natural library call context)` | Remainder term and Bounds. Returns `(cons step library)` with its natural type Step. |
| `(h3-book-mod-mod-theorem library name formula)` | Theorem name string and formula term. Returns `(cons step library)`, with `nil` in the Step position when the tactic does not apply. |

Each call may return a failure in place of its entire result. The Library in
a successful pair includes the auxiliary entries in the order added.

The `-with-library` variants of `remainder-reconstruction`, `add-back`,
`remainder-rational`, `remainder-bounds`, `mod-noncomplex-bounds`,
`mod-bound-goal`, `mod-type-equivalence`, `mod-natural` and
`mod-theorem` take the same arguments. They return
`(cons result library)`, with any failure in the result position and the
auxiliary entries that were added before it.
