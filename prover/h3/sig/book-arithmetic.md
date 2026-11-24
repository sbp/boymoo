# Associative normalization and multiplicative cancellation

`lib` is a Library as specified in `prover/sig/library.md`. Terms and Steps
have the forms in `prover/sig/proof.md`. These functions leave the Library
unchanged. Every function in the table can return a failure as its entire
result. `nil` indicates an unchanged term or an inapplicable recipe, as
specified for each call.

| Call | Result |
|---|---|
| `(h3-book-arithmetic-normal-form lib term)` | Step for the associative and commutative normalization of `term`, or `nil` if unchanged. |
| `(h3-book-arithmetic-associative-equal lib a b)` | Step equating terms `a` and `b` when their normal forms agree. Otherwise returns `Unproved`. |
| `(h3-book-arithmetic-typed-number lib expr)` | Step that term `expr` is an ACL2 number. |
| `(h3-book-arithmetic-fix-value lib value evidence)` | Step reducing `(FIX value)` using the given Step for or against its numeric type. |
| `(h3-book-arithmetic-inverse lib value numeric nonzero)` | Inverse law for term `value`, using its numeric and nonzero Steps. |
| `(h3-book-arithmetic-one-right lib value)` | Step reducing the product of `value` and one. |
| `(h3-book-arithmetic-zero-left lib value)` | Step reducing the product of zero and `value`. |
| `(h3-book-arithmetic-multiply-fix lib value other)` | Step removing `FIX` on the left factor `value` of a product with `other`. |
| `(h3-book-arithmetic-cancel-product lib a b value factor-inverse equality)` | Step canceling the right factor `value` from the product equality Step `equality`, using the inverse-law Step `factor-inverse`. The remaining terms are `(FIX a)` and `(FIX b)`. |
| `(h3-book-arithmetic-zero-test lib term proof)` | Step showing the reciprocal of `term` is zero, using the Step `proof` that `term` is zero or nonnumeric. |
| `(h3-book-arithmetic-scalar-cases lib value use)` | Step joining the three cases of term `value`. `use` is the list of three callback results in the order described below. |
| `(h3-book-arithmetic-truth-value lib evidence)` | Step equating the equality in Step `evidence` to quoted `T`. |
| `(h3-book-arithmetic-equivalent-equalities lib p q forward backward)` | Step equating propositions `p` and `q`. `forward` is the callback result on an assumption of `p`, and `backward` the result on an assumption of `q`. |
| `(h3-book-arithmetic-inverse-nonzero lib term law)` | Step showing that the reciprocal of `term` is nonzero, using its inverse-law Step `law`. |
| `(h3-book-arithmetic-no-zero-product lib a b an bn nz-a nz-b)` | Step showing the product of `a` and `b` is nonzero. `an` and `bn` are numeric Steps, and `nz-a` and `nz-b` are nonzero Steps for those terms in the same order. |
| `(h3-book-arithmetic-zero-product lib a b factor evidence)` | Step showing the product of `a` and `b` is zero. `factor` is the zero or nonnumeric term, and `evidence` is its Step. |
| `(h3-book-arithmetic-reciprocal-involution lib term)` | Step equating the reciprocal of the reciprocal of `term` to `(FIX term)`. |
| `(h3-book-arithmetic-cancel-reciprocal-product lib formula)` | Step for the reciprocal-cancellation formula. |
| `(h3-book-arithmetic-reciprocal-zero-test lib formula)` | Step for equality between the reciprocal and fixed-value zero tests. |
| `(h3-book-arithmetic-reciprocal-product-nonzero lib formula an bn az bz)` | Step for the reciprocal-of-a-product formula. `an` and `bn` are numeric Steps, and `az` and `bz` are nonzero Steps for its factors in the same order. |
| `(h3-book-arithmetic-reciprocal-product lib formula)` | Step for the reciprocal-of-a-product formula. |
| `(h3-book-arithmetic-product-equal-zero lib formula)` | Step for the product-zero formula. |
| `(h3-book-arithmetic-uniqueness-of-inverse lib formula)` | Step for the uniqueness-of-inverse formula. |
| `(h3-book-arithmetic-right-cancellation lib formula)` | Step for the right-cancellation formula. |
| `(h3-book-arithmetic-left-cancellation lib formula)` | Step for the left-cancellation formula. |
| `(h3-book-arithmetic-reciprocal-equality lib formula)` | Step for the reciprocal-equality formula. |
| `(h3-book-arithmetic-reciprocal-fix lib x)` | Step equating the reciprocal of `(FIX x)` to the reciprocal of `x`. |
| `(h3-book-arithmetic-compare-reciprocals lib formula)` | Step for the equality of reciprocals formula. |
| `(h3-book-arithmetic-negative-product lib formula)` | Step for the commutation of negation with the right product factor. |
| `(h3-book-arithmetic-multiply-out lib factor expression)` | Step distributing `factor` over the addition tree `expression`. |
| `(h3-book-arithmetic-factor-out lib expression base factor)` | Step equating `expression` with the product of `base` and `factor`. |
| `(h3-book-arithmetic-factor-cancellation lib formula)` | Step for cancellation of a common factor in an implication, or `nil` when the formula has another shape. |
| `(h3-book-arithmetic-arithmetic-theorem lib name formula)` | The Step selected by theorem name string `name` and term `formula`, or `nil` when there is no applicable recipe. |

The symbols `*h3-book-arithmetic-fix*` and `*h3-book-arithmetic-divide*`
stand for `FIX` and `UNARY-/`. The association list
`*h3-book-arithmetic-associative*` gives the proof rule suffixes for `PLUS`
and `TIMES`, in that order.

## Callbacks

For `scalar-cases`, set `number` to `(list *library-numberp* value)` and
`zero` to `(proof-eq value *proof-zero*)`. Assume these terms with
`proof-proof-assume` on `(library-library-proof lib)`. The callback takes
three arguments in order: a Step about `number`, a status Step, and a
Boolean. Its calls, in order, are `(number-yes zero-yes nil)`,
`(number-yes zero-no t)`, and `(number-no number-no nil)`. The Boolean
means that the value is numeric and nonzero.

The scalar and equivalence callback results are Steps or failures. The
following abbreviations execute callbacks at their use sites, preserving
the order of proof operations around them. In each `(function arg ...)`
form, the indicated callback arguments precede the additional arguments
`arg ...`.

| Call | Expanded callback call |
|---|---|
| `(h3-book-arithmetic-with-scalar-cases lib value (use arg ...))` | `(use numeric status nonzero arg ...)` |
| `(h3-book-arithmetic-with-equivalent-equalities lib p q (forward arg ...) (backward arg ...))` | `(forward assumption arg ...)` and `(backward assumption arg ...)` |
