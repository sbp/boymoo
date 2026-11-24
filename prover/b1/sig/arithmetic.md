# Arithmetic

`library` is a Library as defined in `prover/sig/library.md`. Terms and Steps
use the forms in `prover/sig/proof.md`. `evidence` is an ordered list of Steps. Pass `nil` for empty evidence.
Pass `t` for the default `left` argument of `multiply-one`.

A NumberSums object has the form `(:b1-number-sums library)`. Its constructor
builds the number lemmas in the Library when `SELF-NUMBER-NEGATE-SUM` is
absent. Its inherited sum recipes use number evidence and the corresponding
number lemmas. Use `b1-arithmetic-number-sums-library` to retain any new
Library entries. If another recipe extends the Library while the object is
in use, install the updated Library with `b1-arithmetic-number-sums-with-library`.

Each proof recipe can return a failure as its entire result. A result written
`(cons step library)` contains the Step and the Library after the recipe,
including any auxiliary lemmas in insertion order.

| ACL2 function and arguments | Result |
|---|---|
| `(b1-arithmetic-product a b)` | Product term for terms `a` and `b`. |
| `(b1-arithmetic-reciprocal a)` | Reciprocal term for term `a`. |
| `(b1-arithmetic-known-type library recognizer term evidence)` | Step proving the recognizer call on `term`. |
| `(b1-arithmetic-add-zero library term evidence)` | Step equating zero plus `term` to `term`. |
| `(b1-arithmetic-multiply-one library term evidence left)` | Step removing a factor of one on the side selected by `left`. |
| `(b1-arithmetic-multiply-zero library term)` | Step equating `term` times zero to zero. |
| `(b1-arithmetic-positive-nonzero library proof)` | Step proving nonzero from the positivity Step `proof`. |
| `(b1-arithmetic-inverse-product library term numeric nonzero)` | Step for the product of `term` and its reciprocal, with numeric and nonzero Steps. |
| `(b1-arithmetic-product-unique library inverse product-is-one right-numeric)` | Step identifying the right factor of `product-is-one` with the reciprocal, given `inverse` and a Step proving the right factor numeric. |
| `(b1-arithmetic-nonnumeric-product library term nonnumeric evidence)` | Step reducing the product `term` with the `nonnumeric` Step and the remaining evidence Steps. |
| `(b1-arithmetic-inverse-uniqueness library formula)` | Step proving the inverse characterization `formula`. |
| `(b1-arithmetic-numerator-product library rational)` | `(step (denominator-integer numerator-integer denominator-positive))` from the rationality Step. |
| `(b1-arithmetic-denominator-of-integer library int-x)` | Step proving the denominator of the integer in `int-x` is one. |
| `(b1-arithmetic-numerator-when-integer library formula)` | Step proving the numerator implication `formula`. |
| `(b1-arithmetic-denominator-when-integer library formula)` | Step proving the denominator implication `formula`. |
| `(b1-arithmetic-denominator-one library formula)` | Step proving the denominator-one characterization `formula`. |
| `(b1-arithmetic-times-denominator library formula)` | Step proving the numerator product formula `formula`. |
| `(b1-arithmetic-additive-inverse library a b sum-zero)` | Step solving `a + b = 0` for term `b` from the Step `sum-zero`. |
| `(b1-arithmetic-total-sum-negation library a b)` | `(cons step library)` for negation of the sum of terms `a` and `b`. |
| `(b1-arithmetic-number-sums-init library)` | NumberSums with its initialized Library. |
| `(b1-arithmetic-number-sums-p value)` | Whether `value` is a NumberSums object. |
| `(b1-arithmetic-number-sums-library sums)` | The Library held by NumberSums `sums`. |
| `(b1-arithmetic-number-sums-with-library sums library)` | NumberSums with the given Library. |
| `(b1-arithmetic-number-sums-cite sums name args evidence)` | Cited Step for the name string and argument terms, using the number lemma for a number-specific name. |
| `(b1-arithmetic-number-sums-type-of sums term evidence)` | Step proving that `term` is an ACL2 number. |
| `(b1-arithmetic-number-sums-build sums)` | NumberSums with the number lemmas added to its Library. |
| `(b1-arithmetic-number-sums-push-minus n sums term evidence)` | Step distributing minus in `term`, or `nil` when unchanged. Use initial fuel `1000000`. |
| `(b1-arithmetic-number-sums-linear-form sums term evidence)` | Step equating `term` to its sorted, right-associated sum. |
| `(b1-arithmetic-number-sums-linear-equal sums left right evidence)` | Step equating the two terms through their sum normal forms. |
| `(b1-arithmetic-number-sums-comparison sums left right evidence)` | Step equating a strict comparison of the terms to positivity of their difference. |
| `(b1-arithmetic-number-sums-strict-chain sums left right evidence)` | Step composing the two strict comparison Steps. |
| `(b1-arithmetic-number-sums-comparison-equation sums before after evidence)` | Step equating the strict comparison terms `before` and `after`. |
| `(b1-arithmetic-number-sums-weaken sums strict evidence)` | Step for the weak comparison corresponding to the Step `strict`. |
| `(b1-arithmetic-positive-product library left right evidence)` | Step proving positivity of the product from the factor positivity Steps `left` and `right` and rational evidence. |
| `(b1-arithmetic-positive-sum library left right)` | Step proving positivity of the sum from the summand positivity Steps. |
| `(b1-arithmetic-positive-reciprocal library positive-arg rational)` | `(cons step library)` proving positivity of the reciprocal from a positivity Step and a rationality Step. |
| `(b1-arithmetic-multiply-negation library a b)` | `(cons step library)` distributing a product with terms `a` and `b` over negation of the right factor. |
| `(b1-arithmetic-multiply-strict library factor-positive strict evidence)` | `(cons step library)` for the strict comparison Step after multiplying by the factor in the positivity Step `factor-positive`. |
| `(b1-arithmetic-comparison-cases library a b evidence sums)` | Order trichotomy Step for terms `a` and `b`. The `sums` argument is a Library for integer recipes or a NumberSums for general number recipes. |
| `(b1-arithmetic-integer-compare library a b evidence)` | Order trichotomy Step for integer terms `a` and `b`. |
| `(b1-arithmetic-integer-discrete library pos integer-proof)` | Step bounding a positive integer below by one, given positivity and integrality Steps. |
| `(b1-arithmetic-number-from-comparison library proof position)` | Step proving the operand at index `position` in the strict comparison Step `proof` numeric. |
| `(b1-arithmetic-comparison-excludes library proof value position)` | Step excluding `value` for the operand at index `position` in `proof`. |
| `(b1-arithmetic-reflect-minus-one library term numeric)` | `(cons step library)` equating the two comparisons under sign reversal, with numeric Step `numeric`. |
| `(b1-arithmetic-positive-from-bounds library nonnegative nonzero numeric)` | `(cons step library)` proving positivity from the three given Steps. |
| `(b1-arithmetic-negative-left-factor library a b)` | `(cons step library)` moving negation of the left factor outside the product. |
| `(b1-arithmetic-two-negative-factors library a b)` | `(cons step library)` removing negation of both factors. |
| `(b1-arithmetic-nonzero-negation library arg numeric nonzero)` | `(cons step library)` proving that negation of `arg` is nonzero from the given Steps. |
| `(b1-arithmetic-reciprocal-negation library term numeric nonzero)` | `(cons step library)` equating the reciprocal of the negation with the negation of the reciprocal. |
| `(b1-arithmetic-multiply-minus-one library argument)` | `(cons step library)` equating multiplication by minus one with unary negation. |

The constants are `*b1-arithmetic-fix*`, `*b1-arithmetic-reciprocal*`,
`*b1-arithmetic-numerator*`, and `*b1-arithmetic-denominator*`.
