# Completed numeric operations

A Library, a Step and a term have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. In each call, `lib` is a Library. An argument that
supplies evidence is a Step whose first literal states the required fact.
The term symbol constants are `*t2-field-fix*` for `FIX` and
`*t2-field-divide*` for `UNARY-/`, both in the ACL2 package of prover
terms.

Except for `t2-field-fixed` and `t2-field-reciprocal`, each function
in the tables can return a failure as its entire result. A bare Step result
leaves the Library unchanged. A Step and Library result is
`(cons step lib)`, including when the Library has no new entries.
An updated Library retains the order of its facts and entries, with any
new ones added in proof construction order.

## Term and proof construction

| Call | Arguments and result |
|---|---|
| `(t2-field-fixed term)` | The term `(FIX term)`. |
| `(t2-field-reciprocal term)` | The term `(UNARY-/ term)`. |
| `(t2-field-conjunction lib first second)` | Steps for the two conjuncts. Returns a Step for their conjunction with `first` as its test. |
| `(t2-field-number lib term)` | A Step proving that a call of `FIX`, `UNARY-/`, `BINARY-+`, `BINARY-*` or `UNARY--` is numeric. Returns `missing-binding` for an operator without a numeric closure rule. |
| `(t2-field-numeric-fix lib term numeric)` | Evidence that `term` is numeric. Returns a Step proving `(FIX term) = term`. |
| `(t2-field-identity lib term numeric operator)` | A term, its numeric Step and an operator symbol. Returns the right identity Step for addition when the operator is `BINARY-+`, or multiplication otherwise. |
| `(t2-field-remove-fixed-operand lib operator x y)` | An operator symbol and two terms. Returns the Step that removes the `FIX` of the second operand, for addition when the operator is `BINARY-+`, or multiplication otherwise. |
| `(t2-field-inverse lib numeric different)` | Numeric and nonzero Steps for the same term. Returns the Step proving its product with its reciprocal equals one. |
| `(t2-field-nonzero-factor lib equation)` | An equation Step whose left side is a product and whose right side is one. Returns a Step proving that the first factor is nonzero, paired with the Library. |
| `(t2-field-unique-reciprocal lib equation numeric-candidate numeric-factor)` | A product equation Step as in `nonzero-factor`, evidence that the second factor is numeric, and optionally evidence that the first factor is numeric. Pass `nil` to obtain the latter with `number`. Returns the Step equating the reciprocal of the first factor to the second factor, paired with the Library. |
| `(t2-field-reciprocal-zero lib value zero)` | A term and evidence that its fixed value is zero. Returns the Step proving its reciprocal is zero. |
| `(t2-field-cancel-inverse-on-right lib value factor inverse-product)` | Two terms and a Step proving the product of `factor` and its reciprocal equals one. Returns the Step equating `((value * factor) * reciprocal(factor))` to `(FIX value)`. |
| `(t2-field-multiply-cancel lib value other factor equality inverse-product)` | Terms for two left factors and their common right factor, the equality Step for the products, and the inverse-product Step. Returns a Step equating the fixed values of the left factors. |
| `(t2-field-true-equality lib proof)` | An equality Step. Returns a Step equating its first literal to quoted `T`. |
| `(t2-field-false-value lib evidence)` | Evidence of the negation of a term. Returns a Step equating that term to quoted `NIL`. |
| `(t2-field-equal-predicates lib left right goes-right goes-left left-boolean right-boolean)` | Two proposition terms, Steps proving each from the other, and optional Boolean evidence Steps for the two terms. Pass `nil` for each omitted argument to use the equality recipe for that term. Returns a Step equating the propositions, paired with the Library. |
| `(t2-field-inverse-of-fixed lib value nonzero)` | A value term and evidence that its fixed value is nonzero. Returns a Step proving the product of the value and its reciprocal equals one. |
| `(t2-field-zero-product-from-left lib left right zero)` | Two factors and a Step equating the left factor to zero. Returns the Step equating their product to zero, paired with the Library. |
| `(t2-field-zero-fixed-product lib left right zero)` | Two factors and a Step equating the fixed left factor to zero. Returns the Step equating their product to zero, paired with the Library. |
| `(t2-field-product-second-numeric lib proof)` | A product equation Step with one on the right. Returns a Step proving the second factor numeric. |

## Library entries

These functions each take just the Library and return its updated form.

| Function | Added entries |
|---|---|
| `t2-field-numeric-axioms` | Numeric closure for products, reciprocals and fixed terms. |
| `t2-field-fixed-operand-lemmas` | Removal of fixed operands from addition, multiplication, reciprocal and negation. |
| `t2-field-minus-form` | Completed double negation and negative-factor identities. |
| `t2-field-rights-cancel` | Right cancellation of a common factor. |
| `t2-field-inverse-twice` | The reciprocal involution. |
| `t2-field-inverse-product` | The reciprocal of a product. |
| `t2-field-equal-reciprocals` | The equality test for two reciprocals. |
| `t2-field-equal-inverse` | The test for equality between a reciprocal and a value. |
| `t2-field-prefer-products` | Product equations for the two orders of multiplication by a reciprocal. |
| `t2-field-less-identities` | Differences, zero comparisons and negations for completed order. |
| `t2-field-denominator-one` | The test for a denominator of one. |
| `t2-field-fraction-lemmas` | Multiplication by a denominator, integer numerators and denominators, and the test for a zero numerator. Includes the denominator-of-one entry. |
| `t2-field-build` | The numeric closure, fixed operand, negation, cancellation, reciprocal, comparison and fraction entries, in that order. |

## Lifted functions

| Call | Arguments and result |
|---|---|
| `(t2-field-equal-predicates-positive proof boolean lib)` | A proposition Step and an optional Boolean evidence Step. Returns the Step equating the proposition to quoted `T`, paired with the Library. |
| `(t2-field-rights-cancel-factor-zero a eqn lib zero-test)` | A left factor term, its removal-of-fixed-operand Step, and the zero test for the fixed right factor. Returns a Step equating the product to zero, paired with the Library. |
