# Quotient rounding

A Library and a Step have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. A term is a prover term. The symbol constants are
`*t2-quotient-rounding-ceiling*`, `*t2-quotient-rounding-truncate*`,
`*t2-quotient-rounding-rem*`, `*t2-quotient-rounding-mod*` and
`*t2-quotient-rounding-ash*`.

A QuotientCases object has the form
`(:t2-quotient-rounding-quotient-cases lib dividend divisor ratio rat integral negative)`.
The constructor and accessors cannot fail on the given forms. Use the
accessors for the fields. `ratio` is the dividend times the reciprocal of
the divisor. `rat`, `integral` and `negative` are the rationality,
integrality and negative-sign tests of that term, respectively.

| ACL2 call | Result |
|---|---|
| `(t2-quotient-rounding-quotient-cases-init lib dividend divisor)` | QuotientCases for a Library and two terms. |
| `(t2-quotient-rounding-quotient-cases-lib cases)` | The Library. |
| `(t2-quotient-rounding-quotient-cases-dividend cases)` | The dividend term. |
| `(t2-quotient-rounding-quotient-cases-divisor cases)` | The divisor term. |
| `(t2-quotient-rounding-quotient-cases-ratio cases)` | The quotient term. |
| `(t2-quotient-rounding-quotient-cases-rat cases)` | The rationality test term. |
| `(t2-quotient-rounding-quotient-cases-integral cases)` | The integrality test term. |
| `(t2-quotient-rounding-quotient-cases-negative cases)` | The negative-sign test term. |

Every operation below can return a failure in place of its result. Results
that are Libraries carry the added lemmas in order. The remaining
operations leave the Library unchanged.

| ACL2 call | Result |
|---|---|
| `(t2-quotient-rounding-opened-rounding lib function dividend divisor)` | Step opening a rounding call and reducing its bindings. |
| `(t2-quotient-rounding-unit-product lib value numeric)` | Step equating multiplication of `value` by the reciprocal of one to `value`, using its numeric Step. |
| `(t2-quotient-rounding-to-unit-divisor lib function dividend divisor)` | Step equating the rounding call to its form with divisor one. |
| `(t2-quotient-rounding-completed-part lib name ratio nonrational)` | Step for the completed `"NUMERATOR"` or `"DENOMINATOR"` call, using the nonrationality Step. |
| `(t2-quotient-rounding-quotient-cases-value cases function tests)` | Step evaluating the rounding function in the case given by the supplied Steps. The order is rationality, integrality if rational, and comparison with zero if fractional. |
| `(t2-quotient-rounding-resolve-floor-term lib floor expression)` | Step evaluating the floor or its increment in `expression`, using the floor equality Step. |
| `(t2-quotient-rounding-rounded-quotients lib)` | Library with the truncate and ceiling lemmas. |
| `(t2-quotient-rounding-cancel-nonzero-divisor lib dividend divisor nonzero-ratio)` | Step cancelling the divisor, using a Step that the ratio is nonzero. |
| `(t2-quotient-rounding-cancel-divisor lib dividend divisor nonzero)` | Step cancelling the divisor, using a Step that its numeric fix is nonzero. |
| `(t2-quotient-rounding-remainder-increment lib opened floor)` | Step rewriting the opened remainder when the quotient is the increment of the floor term. |
| `(t2-quotient-rounding-zero-remainder lib)` | Library with the zero-quotient remainder lemma. |
| `(t2-quotient-rounding-remainders lib)` | Library with the remainder-by-modulus lemma. |
| `(t2-quotient-rounding-floor-unit-integer lib integer-value)` | Step evaluating floor at divisor one, using an integrality Step. |
| `(t2-quotient-rounding-shift-floor lib)` | Library with the shift-by-floor lemma. |
| `(t2-quotient-rounding-build lib)` | Library with the quotient rounding and remainder lemmas. |

For `quotient-cases-prove`, `replies` maps each requested test Step list to
its branch result with `(tests . step)` association-list entries in
request order. Start with `nil`. Recognize a request with
`t2-quotient-rounding-branch-request-p` and obtain its test Step list with
`t2-quotient-rounding-branch-request-tests`. Both take the returned object
and cannot fail. Evaluate the branch on that list and pass the new reply
into the next call. A branch failure can occupy the result slot and is then
returned as the entire result. Requests visit
the fractional case first at each sign and the nonrational case last.

## Library updates in branch proofs

`cancel-nonzero-divisor` returns `(cons step lib)` so the caller can retain
`PRODUCT-ZERO` when it is added. The corresponding row above describes
its Step.

`t2-quotient-rounding-quotient-cases-prove-with-library` takes the same
arguments as `quotient-cases-prove`. Its completed result is `(cons step
lib)`, with the Library after the branch calls. A reply value may be
`(cons step lib)` to carry Library changes into subsequent branches. A
bare Step keeps the Library used for the request. Both proof functions
recognize either reply form and return a pending request or a failure as
the entire result. `t2-quotient-rounding-branch-request-lib` returns the
Library at the point of the request.

| ACL2 call | Result |
|---|---|
| `(t2-quotient-rounding-rounded-quotients-branch tests cases function expected floor increment)` | Step for the indicated truncate or ceiling branch. `expected`, `floor` and `increment` are terms. May fail. |
| `(t2-quotient-rounding-remainders-branch tests cases trunc rem fix floor mod expected)` | `(cons step lib)` for the indicated remainder branch, with any auxiliary lemma. `trunc` and `rem` are equality Steps, and `fix`, `floor`, `mod` and `expected` are terms. May fail. |
