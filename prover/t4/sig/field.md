# Reciprocal identities and scaled equations

Terms, Steps and Libraries use the representations in `prover/sig/proof.md`
and `prover/sig/library.md`. `premises` is a list of Steps in premise order.
The routines below return `(cons value lib)` with the Library after any
auxiliary lemmas have been added. A failure can occupy the value field.

| ACL2 call | Value |
|---|---|
| `(t4-field-inverse-from-product lib product)` | The Step proving that the second factor is the reciprocal of the first, given a product-equals-one Step. |
| `(t4-field-simplified lib proof premises)` | The Step obtained by normalizing the right side of the equality Step `proof`. Pass `nil` for no premises. |
| `(t4-field-reciprocal-of-operation lib goal)` | A Step for the reciprocal of a product or negation, or `nil` if the tactic does not apply. |
| `(t4-field-compare-inverse lib relation products premises)` | A Step equating a reciprocal equality `relation` to the corresponding product equality `products`, or `nil` if the tactic does not apply. |
| `(t4-field-inverse-with-zero-case lib goal)` | A Step for the equality with a zero case, or `nil` if the tactic does not apply. |
| `(t4-field-scaled-right lib goal premises)` | A Step for the equality between the original test and its guarded scaled test, or `nil` if the tactic does not apply. |
| `(t4-field-field-identity lib formula)` | A Step for `formula`, or `nil` if the tactic does not apply. |

`(t4-field-applicable-p formula)` tests whether the goal under the optional
implication has head `EQUAL`. It can return a failure for malformed implication
arguments. The BookLogic caller runs `t4-booklogic-booklogic-use-arithmetic` after
this test succeeds and passes the resulting Library to
`t4-field-field-identity`, which returns the Library with further additions.

Each Step recipe in the table also has a `-with-replies` form taking a
final reply alist. Value fields can contain a request of the form
`(:call kind lib . args)`, as in `prover/t4/sig/algebra.md`. To handle it,
associate the full request with the corresponding `(cons value lib)`
reply and repeat the initial call with the extended alist.
`t4-field-field-identity-with-replies` requests `:arithmetic` after it
recognizes an equality. In this form, the caller starts with the current
Library and processes arithmetic initialization like the other requests.
