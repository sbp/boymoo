# Quotient proofs

`lib` is a Library. Terms and Steps use the forms in `prover/sig/proof.md`.
The `signs` argument is the Signs value from `prover/h3/sig/book-signs.md`.
`name` is a theorem name string. `evidence` is an insertion-ordered alist
from literals to Steps. An optional Step or list is `nil` when absent.

Every function below can return a failure in place of its result. A result
written `(cons value lib)` contains the value and the Library with any
auxiliary lemmas, in the order in which they were added. Read the Library
from that pair even when the value is `nil`.

| ACL2 call | Arguments and result |
|---|---|
| `(h3-book-quotient-reciprocal-factor term)` | Returns the list `(divisor numerator)` when `term` contains a reciprocal in either factor position or is itself a reciprocal. An isolated reciprocal has numerator one. Otherwise returns `nil`. |
| `(h3-book-quotient-cancel-inverse-pair lib term divisor argument law)` | Given the product `term`, the divisor and remaining argument terms, and the inverse-law Step, returns the cancellation Step. |
| `(h3-book-quotient-clear-reciprocal lib term divisor law numerator-type)` | Given a quotient term, divisor, inverse-law Step and optional numeric Step for the numerator, returns the result of multiplying the quotient by the divisor and clearing the reciprocal when it matches. |
| `(h3-book-quotient-quotient-equality lib formula)` | Returns a Step proving a quotient equality formula. |
| `(h3-book-quotient-rational-type lib term evidence)` | Returns a Step proving `term` rational from the evidence alist and the rationality rules. |
| `(h3-book-quotient-rational-difference lib first second)` | Given two rationality Steps, returns a Step proving the difference rational. |
| `(h3-book-quotient-product-equals-factor lib formula)` | Returns a Step proving the equality between a product and a repeated factor. |

The `-with-library` forms of `distribute-difference`, `opposite-difference`,
`scale-order`, `quotient-order`, `factor-order`, `reciprocal-of-opposite`
and `quotient-theorem` take the same arguments. They return `(cons value lib)`
with any failure as `value`, so a caller can continue with the Library when
it catches the failure.

`(h3-book-quotient-step-at step index)` returns the zero-based element of
the Step's first literal. `(h3-book-quotient-tail-of-size term size)` returns
the term's tail, checked to contain `size` elements. Both can return a failure.
