# Numerator and denominator proofs

`proof` is the H1 Prover from `tactics.md`. `norm` is the Algebra from
`book-arithmetic.md`. Terms and Steps use the forms in `prover/sig/proof.md`.
This book defines no classes. The constants `*h1-book-fraction-numerator*`
and `*h1-book-fraction-denominator*` are the respective Common Lisp
symbols in prover term form.

| Call | Result | Failure |
|---|---|---|
| `(h1-book-fraction-numerator value)` | The `NUMERATOR` application to `value`. | — |
| `(h1-book-fraction-denominator value)` | The `DENOMINATOR` application to `value`. | — |
| `(h1-book-fraction-default-value proof value head nonrational)` | The Step for the default `head` result on `value`, using the Step `nonrational`. | A failure in place of the Step. |
| `(h1-book-fraction-multiply-denominator proof)` | The Prover with the rational decomposition and denominator multiplication laws. | A failure in place of the Prover. |
| `(h1-book-fraction-integer-values proof)` | The Prover with the denominator and numerator values for integer inputs. | A failure in place of the Prover. |
| `(h1-book-fraction-numerator-signs proof)` | The Prover with the positive and negative numerator laws, in that order. | A failure in place of the Prover. |
| `(h1-book-fraction-equal-denominator-one proof)` | The Prover with the test for a denominator of one. | A failure in place of the Prover. |
| `(h1-book-fraction-total-denominator-product proof)` | The Prover with the denominator product law for all inputs. | A failure in place of the Prover. |
| `(h1-book-fraction-numerator-nonzero proof)` | The Prover with its law for a nonzero numerator. | A failure in place of the Prover. |
| `(h1-book-fraction-scaled-numerator-is-integer proof norm value)` | `(cons step norm)` with the integrality Step for the scaled numerator and the resulting Algebra. | A failure in place of the pair. |
| `(h1-book-fraction-negative-integer-value proof norm expression integral)` | `(cons step norm)` with the integrality Step for `expression` from the Step `integral` and the resulting Algebra. | A failure in place of the pair. |
| `(h1-book-fraction-reduced-denominator proof norm value common cofactor factorization typed-product)` | `(cons step norm)` with the reduction Step and the resulting Algebra. `common` and `cofactor` are terms, `factorization` and `typed-product` are Steps for the factorization and integrality. | A failure in place of the pair. |
| `(h1-book-fraction-denominator-negation proof)` | The Prover with the denominator negation law. | A failure in place of the Prover. |
| `(h1-book-fraction-numerator-negation proof)` | The Prover with the numerator negation law. | A failure in place of the Prover. |
| `(h1-book-fraction-install-fractions proof)` | The Prover after registering the rationality rule and installing the fraction lemmas in order. | A failure in place of the Prover. |
