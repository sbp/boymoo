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
| `(t4-ordered-rational lib value premises)` | `(cons step lib)` proving the term `value` rational. |
| `(t4-ordered-identity lib left right premises)` | `(cons step lib)` proving equality of the terms by normalization. |
| `(t4-ordered-positive term)` | The term comparing quoted zero strictly below `term`. Does not failure. |
| `(t4-ordered-negative term)` | The term comparing `term` strictly below quoted zero. Does not failure. |
| `(t4-ordered-signed-cases lib value typed leaf)` | `(cons step lib)` joining the three sign branches of term `value`, with rational Step `typed`. The leaf replies or requests follow positive, zero, negative order. |
| `(t4-ordered-no-negative lib value above)` | `(cons step lib)` proving term `value` is not negative using positive Step `above`. |
| `(t4-ordered-nonzero-sign lib sign)` | A Step proving the nonzero Sign's term unequal to quoted zero. |
| `(t4-ordered-sign-test lib sign term)` | `(cons step lib)` for whether comparison term `term` holds under the given Sign, or `nil` in the value position for an unknown test. |
| `(t4-ordered-as-boolean lib test premise)` | `(cons step lib)` proving the Boolean value of term `test` using Step `premise`. |
| `(t4-ordered-product-sign lib x y premises)` | `(cons sign lib)` for the product of the terms of the two Signs `x` and `y`. |
| `(t4-ordered-sign-formula lib term signs)` | `(cons step lib)` computing the Boolean formula term with the ordered list of Signs. |
| `(t4-ordered-product-sign-theorem lib formula)` | `(cons step lib)` proving the formula term by splitting on the signs of its product's operands, or `nil` in the step position for an unmatched formula. |
| `(t4-ordered-scaled-order-lemma lib)` | The Library with the rational scaling lemma, or a failure. |
| `(t4-ordered-scaled-order lib a b factor premises)` | `(cons step lib)` proving the order of terms `a` and `b` when scaled by term `factor`. |
| `(t4-ordered-scale-for-unscaled lib term factor premises)` | `(cons (list value step) lib)` with the unscaled term and its scaling equality Step. The pair of fields is `(nil nil)` if the term lacks the factor. |
| `(t4-ordered-choose-sign lib equation sign)` | `(cons step lib)` reducing the right side of equality Step `equation` as far as the Sign permits. |
| `(t4-ordered-scaled-comparison lib formula)` | `(cons step lib)` for a comparison with a common scale, or `nil` in the step position when no candidate succeeds. |
| `(t4-ordered-divided-comparison lib formula)` | `(cons step lib)` proving the formula term by clearing its reciprocal, or `nil` in the step position when no candidate succeeds. |

The three formula calls and `t4-ordered-rational` also have `-with-replies`
entry points taking a final reply alist. A request has the form
`(:call kind lib . args)` and the alist maps requests to replies. For
`:arithmetic` there are no additional arguments and the reply is
`(cons nil lib)` with arithmetic initialized. For `:fact-proof` the
arguments are the target term and Evidence, and the reply is `(cons step lib)`
with the Library after that call. A Step reply can be `nil` or a failure.
At a request, add its reply to the alist and repeat the original call.
The ordinary calls start with an empty alist.

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
