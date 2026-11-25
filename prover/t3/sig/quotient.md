# Quotient bounds

Terms and Steps have the forms in `prover/sig/proof.md`. `lib` is a Library
with T3 proof rules. `evidence` is an Evidence object from `logic.lisp`.
`interval` and `upper` are Booleans and default to `nil`.
`positive-value` is a Step or `nil`.

The symbol constants are `*t3-quotient-niq*`, `*t3-quotient-print-base*`,
`*t3-quotient-quotient-lemma*`, `*t3-quotient-quotient-interval*`, and
`*t3-quotient-print-base-lemma*`.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t3-quotient-product term scale)` | Returns the term for the product with `scale` first and `term` second. | None. |
| `(t3-quotient-division-inputs numerator denominator)` | Two terms. Returns the conjunction of the natural dividend and positive integer divisor hypotheses. | None. |
| `(t3-quotient-quotient-claim numerator denominator value interval)` | Dividend, divisor, and candidate quotient terms. Returns the conditional quotient property, including the strict upper bound when `interval` is true. | None. |
| `(t3-quotient-mul-one lib value typed)` | A term and its rational type Step. Returns the Step equating the product of 1 and `value` with `value`. | A failure from proof construction. |
| `(t3-quotient-add-product lib scale offset typed)` | Divisor and offset terms and the divisor's rational type Step. Returns the Step distributing the divisor over one plus the offset. | A failure from proof construction. |
| `(t3-quotient-quotient-base-upper lib guard ix iy positive-y)` | A test term and Steps for integer `X`, integer `Y`, and positive `Y`. Returns the Step for the upper bound in the zero-quotient case. | A failure from proof construction. |
| `(t3-quotient-quotient-induction lib interval)` | Returns the Library with the quotient lemma for the selected bounds. | A failure from proof construction or a failed assertion. |
| `(t3-quotient-base-claim term)` | Radix term. Returns the conjunction of integrality, positivity, and bounds for its reciprocal. | None. |
| `(t3-quotient-print-base-range lib)` | Returns the Library with the print-base range lemma. | A failure from proof construction or a failed assertion. |
| `(t3-quotient-print-ratio lib value base evidence positive-value)` | Integer value and radix terms. Returns `(((ratio ratio-type above below base-type base-positive) evidence) . lib)` with the resulting Evidence and Library. | A failure from proof construction or an evidence query. |
| `(t3-quotient-multiply-ratio lib ratio base base-type base-positive types)` | Ratio and radix terms, Steps for the radix's integer type and positivity, and the ordered list of type Steps. Returns the equality Step that cancels the reciprocal. | A failure from proof construction or a malformed ratio. |
| `(t3-quotient-rounded-bounds lib call evidence positive-value upper)` | A floor or truncate call. Returns `((steps evidence) . lib)` with the resulting Evidence and Library. The Steps are natural and strict decrease, followed by the strict upper bound when `upper` is true. | A failure from proof construction, a failed assertion, or an evidence query. |
| `(t3-quotient-digit-measure value)` | An integer term. Returns its count plus the phase for its sign. | None. |
| `(t3-quotient-is-digit-measure term)` | Returns whether the term has the digit measure form. | A failure on a matching head with a missing argument. |
| `(t3-quotient-digit-rank-value lib rank typed sign)` | Digit measure term, an integer Step for its argument, and the sign Step. Returns the equality Step for the evaluated rank. | A failure from proof construction or a malformed rank. |
| `(t3-quotient-digit-descent lib smaller larger evidence)` | Two digit measure terms. Returns `((step evidence) . lib)` with the ordinal decrease Step, resulting Evidence, and resulting Library. | `unsupported` for an unrecognized step, or a failure from proof construction or an evidence query. |

A failure is the whole result. Induction substitutions occur in leaf
visit order. The substitutions within a recursive quotient case are a
one-element list of binding pairs.

The returned Evidence carries the updated Library when its input Library
matches `lib`.
