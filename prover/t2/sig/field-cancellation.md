# Field cancellation

`lib` is a Library as specified in `prover/sig/library.md`. Terms and Steps
have the forms in `prover/sig/proof.md`. Each function can return a failure.
Functions that add lemmas return the resulting Library with entries and
facts in insertion order.

| Call | Arguments and result |
|---|---|
| `(t2-field-cancellation-symmetric-test lib a b)` | For terms `a` and `b`, the Step equating the two orientations of their equality test. |
| `(t2-field-cancellation-guarded-identity lib test)` | For a test term, the Step equating `(if test test 'nil)` with the test. |
| `(t2-field-cancellation-subtract-summand lib value summand)` | For two terms, the Step equating the subtraction of `summand` from `value + summand` with the numeric fix of `value`. |
| `(t2-field-cancellation-cancel-sums lib)` | Library with the sum and opposite-summand cancellation lemmas. |
| `(t2-field-cancellation-map-involution lib operation label fix-label name)` | `operation` is `:minus` or `:reciprocal`. The other arguments are lemma-name strings. Returns the Library with the equality lemma for the operation. |
| `(t2-field-cancellation-map-zero lib)` | Library with the zero tests for negation and reciprocation. |
| `(t2-field-cancellation-sum-zero lib)` | Library with the sum zero tests. |
| `(t2-field-cancellation-reciprocal-products lib)` | Library with the reciprocal product cancellation lemmas. |
| `(t2-field-cancellation-cancel-products lib)` | Library with product cancellation, zero and sign lemmas. |
| `(t2-field-cancellation-numeric-self-equality lib operator combine fixed-operand)` | `operator` is the term head for addition or multiplication, `combine` is `:plus` or `:times`, and `fixed-operand` is a term. Returns the list `(start impossible numeric other unit)` of three Steps followed by the other operand term and the unit term. |
| `(t2-field-cancellation-sum-equals-operand lib)` | Library with the lemmas for a sum equal to one of its operands. |
| `(t2-field-cancellation-fixed-one lib)` | Step equating the fixed and unfixed tests for equality to one. |
| `(t2-field-cancellation-product-equals-operand lib)` | Library with the lemmas for a product equal to one of its operands. |
| `(t2-field-cancellation-numerator-nonzero lib)` | Library with the implication from a nonzero numerator. |
| `(t2-field-cancellation-build lib)` | Library extended with the field cancellation lemmas. |
