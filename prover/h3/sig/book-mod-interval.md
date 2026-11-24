# Remainder interval proofs

`lib` is a Library, and terms and Steps use the forms in `prover/sig/proof.md`.
`context` is a Bounds object described in `prover/h3/sig/book-order.md`.
`signs` is a Signs value described in `prover/h3/sig/book-signs.md`.
An evidence list is in argument order. Evidence read from Bounds is in
insertion order.

Each proof call can return a failure in place of its result. A result of the
form `(cons value lib)` holds the returned value and the Library with any
auxiliary lemmas, in the order they were added. A missing optional Step is
`nil` in the value position of the pair.

| ACL2 call | Arguments and result |
|---|---|
| `(h3-book-mod-interval-remainder-interval-theorem lib name formula)` | The unqualified theorem name string and formula term. Returns `(cons step lib)` with the interval proof, or with `nil` when no recipe applies. |
| `(h3-book-mod-interval-finite-product lib amount rational-divisor)` | Endpoint term and rationality Step for its multiplier. Returns the product reduction Step, or `Unproved` for an unsupported endpoint. |
| `(h3-book-mod-interval-ratio-from-scaled lib ratio-type dividend divisor signs relation given)` | Rationality Steps for the ratio, dividend and divisor, the divisor's Signs, a strict or negated comparison term, and the scaled bound Step. Returns `(cons step lib)` with the unscaled bound. |
| `(h3-book-mod-interval-remainder-in-interval lib dividend divisor signs integer lower upper)` | Rationality Steps for dividend and divisor, divisor Signs, integrality Step for the interval index, and scaled lower and upper bound Steps. Returns `(cons step lib)` with the remainder equality. |
| `(h3-book-mod-interval-inside-remainder lib dividend divisor signs lower upper)` | Rationality Steps for dividend and divisor, divisor Signs, and scaled bounds for the interval with index zero. Returns `(cons step lib)` with the equality to the dividend. |
| `(h3-book-mod-interval-unchanged-mod n lib call context)` | Natural-number fuel, remainder term and Bounds. Returns `(cons step lib)` with the equality to the dividend, or `Unproved` if the bounds cannot be obtained. Pass `1000000` as initial fuel. |
| `(h3-book-mod-interval-mixed-remainder lib call rational nonrational numeric-dividend)` | Remainder term and Steps for one argument's rationality, the other argument's nonrationality, and the dividend's numeric type. Returns the Step equating the remainder to the dividend. |
| `(h3-book-mod-interval-nested-remainder lib call context)` | Nested remainder term and Bounds. Returns `(cons step lib)` with the equality to the inner remainder. |
| `(h3-book-mod-interval-move-sum-bound lib bound target typed)` | Given bound Step, equivalent comparison term and ordered type Steps. Returns `(cons step lib)` with the equivalent bound. |
| `(h3-book-mod-interval-summed-remainder-bounds lib first second divisor positive first-bounds second-bounds)` | Rationality Steps for the two remainders and their common divisor, divisor positivity Step, and their two `(lower upper)` lists. Returns `(cons (list lower upper) lib)` with the two bounds for the sum. |
| `(h3-book-mod-interval-sum-of-remainders lib left right divisor)` | Rationality Steps for the summands and divisor. Returns the Step using the named sum congruence, or `Unproved` when the congruence is absent. |
| `(h3-book-mod-interval-mod-sum-cases lib goal context)` | Remainder-sum equality and Bounds. Returns `(cons step lib)` with the equality proved by cases. |
| `(h3-book-mod-interval-replace-remainder lib step equality)` | Step to rewrite and equality Step to apply. Returns the rewritten Step. |
| `(h3-book-mod-interval-mod-cancel-divisor lib goal)` | Equality term for cancelling the divisor from a remainder. Returns `(cons step lib)` with the equality proof. |
| `(h3-book-mod-interval-scaled-remainder lib goal context)` | Equality term and Bounds. Returns `(cons step lib)` with the scaled remainder proof when the terms have the common-factor form, or with `nil` otherwise. |
| `(h3-book-mod-interval-affine-literal-remainder lib goal context)` | Equality or negated equality term and Bounds. Returns `(cons step lib)` with the remainder proof when a matching literal can be separated from the displacement, or with `nil` when the shape does not match. |
| `(h3-book-mod-interval-parity-remainder lib goal context)` | Equality term relating remainder at divisor two to parity, and Bounds. Returns `(cons step lib)` with the parity proof. |

`(h3-book-mod-interval-remainder-interval-theorem-with-library lib name formula)`
has the same arguments. It returns `(cons result lib)` on success and on a
failure. Use this form when a tactic catches `Unproved` and continues with the
auxiliary lemmas added before that failure.
