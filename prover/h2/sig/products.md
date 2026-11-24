# Products and reciprocal cancellation

`proof` is the H2 proof search object for book statements. Terms and Steps
use the forms in `prover/sig/proof.md`. A product argument is a binary
multiplication term. Factor positions are 1 for the left factor and 2 for
the right factor. `typed` proves that the named factor is an ACL2 number.
`nonzero` denies its equality to zero, in either orientation. `unit` is a
Step equating a product to one. Evidence lists are in the supplied order.

Each function can return a failure. Where the result is `(cons value proof)`,
the proof contains any facts, entries, and search settings established by
the call.

| Function | Arguments in order | Result |
|---|---|---|
| `h2-products-numerical-zero-product` | `proof` | `(cons name proof)` with the fact name `SELF-H2-ZERO-PRODUCT`. |
| `h2-products-product-of-negative` | `proof`, factor term, value term | `(cons step proof)` for multiplication by the negation of the value. |
| `h2-products-zero-factor` | `proof`, product term, factor position, Step for a zero or nonnumeric factor | `(cons step proof)` equating the product to zero. |
| `h2-products-zero-factors-excluded` | `proof`, `unit`, factor position | `(cons step proof)` denying a zero factor. |
| `h2-products-inverse-product` | `proof`, factor term, `typed`, `nonzero` | A Step equating the product of the factor and its reciprocal to one. |
| `h2-products-collapse-unit` | `proof`, `unit`, remaining term | An equality Step reducing the nested product to the remaining term's numeric fix. |
| `h2-products-recover-factor` | `proof`, factor term, remaining term, `typed`, `nonzero` | A Step recovering the remaining factor's numeric fix by multiplying by the reciprocal. |
| `h2-products-cancel-left-factor` | `proof`, Step equating two products with the same left factor, `typed`, `nonzero` | An equality Step for the numeric fixes of the right factors. |
| `h2-products-inverse-unique` | `proof`, `unit`, number Step for the factor, number Step for the proposed reciprocal | `(cons step proof)` equating the reciprocal with the proposal. |
| `h2-products-reciprocal-zero` | `proof`, argument term, evidence Step list | `(cons step proof)` equating the reciprocal of the argument to zero. |
| `h2-products-inverse-involution` | `proof`, theorem formula | `(cons step proof)` for reciprocal involution. |
| `h2-products-inverse-involution-zero-case` | Evidence Step list, target equality Step, `proof`, value term, theorem formula | `(cons step proof)` for the zero or nonnumeric case of reciprocal involution. |
| `h2-products-inverse-distributed` | `proof`, theorem formula | `(cons step proof)` for reciprocal distribution over multiplication. |
| `h2-products-inverse-distributed-missing` | Factor position, Step for a zero or nonnumeric factor, evidence Step list, `proof`, product argument term, left term, right term | `(cons step proof)` for that case of reciprocal distribution. |
| `h2-products-divide-product` | `proof`, theorem formula | A Step for cancellation by the reciprocal on the selected side. |
| `h2-products-fix-second-factor` | `proof`, factor term, value term | `(cons step proof)` for a product with and without a numeric fix on the second factor. |
| `h2-products-cancel-comparison` | `proof`, theorem formula, factor position, `against-zero` Boolean | `(cons step proof)` for the corresponding cancellation comparison. Pass `nil` for the default Boolean. |
| `h2-products-cancel-comparison-vanished` | Step for a zero or nonnumeric factor, Step for its numeric fix equaling zero, `proof`, first term, factor position, `against-zero` Boolean, second term, comparison term, zero-test orientation, conditional term, zero-test term | `(cons step proof)` for that case of a cancellation comparison. |
| `h2-products-product-theorem` | `proof`, theorem label string, theorem formula | `(cons step proof)` for a recognized theorem, with `nil` in the step position for an unrecognized label. |

Pass the inherited Search from `prover/h2/sig/search.md` as `proof`. An
inherited method can return a Search request in place of the result. Append
the method reply and repeat the original call as specified there.
