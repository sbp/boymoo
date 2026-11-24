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
| `(h3-book-quotient-distribute-difference lib a b factor)` | Given two difference operands and a factor term, returns `(cons step lib)` for distributing the factor over the difference. |
| `(h3-book-quotient-opposite-difference lib a b)` | Returns `(cons step lib)` for negating the difference of terms `a` and `b`. |
| `(h3-book-quotient-scale-order lib a b scalar signs types)` | Given comparison operands, the multiplier's rationality Step, its Signs value, and an optional list of the two operands' rationality Steps in operand order, returns `(cons step lib)` for scaling the comparison. |
| `(h3-book-quotient-quotient-order lib formula)` | Returns `(cons step lib)` proving a quotient order formula by the divisor sign cases. |
| `(h3-book-quotient-factor-order lib formula)` | Returns `(cons step lib)` with the common-factor comparison proof or `nil` for an unrecognized formula. |
| `(h3-book-quotient-product-equals-factor lib formula)` | Returns a Step proving the equality between a product and a repeated factor. |
| `(h3-book-quotient-reciprocal-of-opposite lib formula)` | Returns `(cons step lib)` proving the reciprocal-of-negation formula. |
| `(h3-book-quotient-quotient-theorem lib name formula)` | Returns `(cons step lib)` with the selected quotient proof or `nil` for an unrecognized name. |

The `-with-library` forms of `distribute-difference`, `opposite-difference`,
`scale-order`, `quotient-order`, `factor-order`, `reciprocal-of-opposite`
and `quotient-theorem` take the same arguments. They return `(cons value lib)`
with any failure as `value`, so a caller can continue with the Library when
it catches the failure.

`(h3-book-quotient-step-at step index)` returns the zero-based element of
the Step's first literal. `(h3-book-quotient-tail-of-size term size)` returns
the term's tail, checked to contain `size` elements. Both can return a failure.

`(h3-book-quotient-with-library lib ((name form) ...) result)` evaluates
the forms and returns `(cons value lib)` with the first failure or the result.
A binding `(name form :paired)` reads both the value and the new Library
from a pair. `(h3-book-quotient-checked-pair result)` returns the failure from
such a pair or the pair itself. `(h3-book-quotient-each-sign-with-library
lib numeric case arg ...)` applies `(case lib signs arg ...)` in positive,
zero, negative order. It returns the joined Step or failure paired with the
Library. The callback returns a Step or failure paired with its Library.
`(h3-book-quotient-sign-callback lib signs case arg ...)` calls a proof
function as `(case signs lib arg ...)`.
