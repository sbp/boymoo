# Floor rounding

A Library, Step and term have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. A Bounds object has the form in
`prover/h3/sig/book-order.md`, and Signs in `prover/h3/sig/book-signs.md`.
Evidence taken from Bounds is used in insertion order.

`*h3-book-rounding-fl*` is the term symbol for `ACL2::FL`.
`*h3-book-rounding-two*` and `*h3-book-rounding-half*` are the quotations
of two and one half. `*h3-book-rounding-halving*` is the unprefixed lemma
name string.

| Call | Arguments and result |
|---|---|
| `(h3-book-rounding-fl-interval library rational)` | Rationality Step for a term. Returns `(cons (list integer lower upper) library)` with the integrality and interval Steps for its `FL`. |
| `(h3-book-rounding-multiply-ratio-bound library given n-type d-type signs)` | Comparison Step (strict or weak), Steps for rationality of numerator and divisor, and divisor Signs. Returns `(cons step library)` with the scaled comparison. |
| `(h3-book-rounding-floor-of-nonnumeric-or-complex library call not-rational d-type d-nonzero)` | A two-argument `FLOOR` call and Steps for nonrationality of the dividend, rationality of the divisor and its nonzero value. Returns the Step for a zero floor. |
| `(h3-book-rounding-divide-floor library term divisor)` | Dividend and divisor terms. Returns the Step equating `FL` of the reciprocal product with `FLOOR` of those arguments. |
| `(h3-book-rounding-half-floor library term)` | A dividend term. Returns the Step for the corresponding floor with divisor two. |
| `(h3-book-rounding-floor-divisor-shift library term d-int d-positive)` | Dividend term, integer Step for the divisor, and positive Step for the divisor. Returns `(cons step library)` with the equality that removes the inner floor. |
| `(h3-book-rounding-floor-halving library)` | Returns `(cons step library)` with the halving equality for `X`. |
| `(h3-book-rounding-fl-at-integer library integer)` | Integrality Step for a term. Returns the Step identifying its `FL` with the term. |
| `(h3-book-rounding-rounding-theorem library formula)` | A formula term. Returns `(cons step library)` with its proof or `nil` in the Step position if the tactic does not apply. |
| `(h3-book-rounding-integer-floor-result library value guard)` | Term `value` and a hypothesis term or `nil`. Returns `(cons step library)` with an integrality proof or `nil` in the Step position if none applies. |
| `(h3-book-rounding-clear-integer-divisor library value context)` | Term `value` and Bounds `context`. Returns an integrality Step for the value or `nil` if no applicable scaling premise is present. |

Each call may return a failure in place of its entire result. The Library in
a successful pair includes the auxiliary entries in the order added.

`(h3-book-rounding-step-at step index)` obtains the indexed argument of
the Step's first literal at a zero-based index.
`(h3-book-rounding-tail-of-size term size)` checks the arity of a term
and returns its operands. Both may return a failure.

`(h3-book-rounding-guarded-step library guard step)` returns
`(cons step library)` and supplies the implication when both the guard
and the Step are present. It can return a failure as its entire result.

`(h3-book-rounding-with-results bindings result)` evaluates bindings
from left to right and propagates the first failure. A binding has the form
`(name form)`, or `((value object) form)` to bind both parts of a pair.

The `-with-library` variants of `fl-interval`, `multiply-ratio-bound`,
`floor-divisor-shift`, `floor-halving`, `integer-floor-result`,
`rounding-theorem` and `guarded-step` take the same arguments. They
return `(cons result library)` with the failure in the result position if
the call fails, retaining auxiliary lemmas added up to that point.

`(h3-book-rounding-with-library library bindings result)` uses the same
binding forms as `with-results`, pairing a failure with the current Library.
A paired binding replaces the Library using its second value, which is
either the Library named in the first macro argument or a Bounds object.
The final expression returns a pair or a failure.

`(h3-book-rounding-checked-pair result)` exposes the failure from a
Library pair when present and otherwise returns the pair.

`(h3-book-rounding-argument-present-p value)` recognizes a supplied optional argument or hypothesis. `nil`, zero,
and the empty string denote absence.
