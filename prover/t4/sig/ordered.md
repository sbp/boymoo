# Rational order and signs

Terms and Steps have the forms in `prover/sig/proof.md`. `lib` is a Library
in the form in `prover/sig/library.md`. A `Sign` has the form
`(:sign obj order proof)`, with the signed term, a sign integer, and a
Step. The constructor `t4-ordered-sign` takes those three fields. The
accessors `t4-ordered-sign-obj`, `t4-ordered-sign-order` and
`t4-ordered-sign-proof` take the Sign. The constructor and accessors do
not failure. `*t4-ordered-iff*` is the symbol for `IFF`.

`premises` is a list of Steps in premise order. In a result written as
`(cons value lib)`, the Library carries all effects of that call and
`value` may be a failure or a request. Each Step operation can return a failure.

| ACL2 call | Result |
|---|---|
| `(t4-ordered-positive term)` | The term comparing quoted zero strictly below `term`. Does not failure. |
| `(t4-ordered-negative term)` | The term comparing `term` strictly below quoted zero. Does not failure. |
| `(t4-ordered-nonzero-sign lib sign)` | A Step proving the nonzero Sign's term unequal to quoted zero. |
| `(t4-ordered-as-boolean lib test premise)` | `(cons step lib)` proving the Boolean value of term `test` using Step `premise`. |

The `leaf` argument of `signed-cases` is the list of `(cons step lib)`
replies in positive, zero, negative order. If the next reply is absent,
the step position is `(:call :leaf lib sign)`. A leaf failure can occupy
the step position of a reply.

The candidate factors in a scaled comparison are traversed in order of
first occurrence among products on the left and then the right side of
the comparison. Denominator candidates are traversed in premise order.

The `-with-replies` entry points also exist for `identity`,
`signed-cases`, `no-negative`, `sign-test`, `product-sign`,
`sign-formula`, `scaled-order-lemma`, `scaled-order`,
`scale-for-unscaled` and `choose-sign`. Each takes the usual arguments
followed by the reply alist. The entry point for `scaled-order-lemma`
returns `(cons nil lib)` on success, with a failure or request in the car
on interruption. The bare `scaled-order-lemma` gives any request
directly in place of the Library.

Arithmetic normalization can also request `:constant` with a term as
its argument. The reply is `(cons step lib)` using the BookLogic
constant operation. Its value can be a Step, `nil`, or a failure.

`(t4-ordered-request-p value)` recognizes a request and does not return a failure.

The sign recipes can request `:prove` with a term, a list of premise
Steps and a list of definitions to unfold. The reply is `(cons step lib)`
from BookLogic's proof operation, with a failure allowed in the step position.
