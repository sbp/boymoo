# Exponent composition

`proof` is an H1 proof world. Terms and Steps have the forms in `prover/sig/proof.md`. `norm` is the field normalizer described in `prover/h1/sig/book-field.md`. A failure replaces the entire result.

| Call | Result |
|---|---|
| `(h1-book-expt-composition-zip-at-zero proof zero)` | Step proving `ZIP` true on a term proved equal to zero by `zero`. |
| `(h1-book-expt-composition-zip-without-integer proof exponent noninteger)` | Step proving `ZIP` true on `exponent` under the noninteger Step. |
| `(h1-book-expt-composition-zip-negation proof)` | Step proving that unary negation preserves `ZIP`. |
| `(h1-book-expt-composition-install-inverse-exponent proof)` | Proof world with the reciprocal law for a negative exponent. |
| `(h1-book-expt-composition-fixed-at-zero proof equality)` | Step proving that the fix of the term on the left of `equality` is zero. The right side of `equality` is zero. |
| `(h1-book-expt-composition-negate-exponent proof equal-reciprocal)` | Step equating negating the exponent with taking the reciprocal of the base, given the reciprocal-base Step. |
| `(h1-book-expt-composition-product-at-zero proof factor exponent zero index)` | Step reducing the product of `factor` and `exponent` to zero under the zero Step for the operand in operand position `index`, either 1 or 2. |
| `(h1-book-expt-composition-composition-at-zero-base proof norm)` | Pair `(cons step norm)` with the composition Step at a fixed-zero base and the resulting normalizer. |
| `(h1-book-expt-composition-composition proof)` | Pair `(cons step proof)` with the exponent composition Step and the proof world after the countdown lemmas. |
| `(h1-book-expt-composition-install-power-composition proof)` | Proof world with the exponent composition lemmas in order. |

Each function can return a failure from a proof operation.
