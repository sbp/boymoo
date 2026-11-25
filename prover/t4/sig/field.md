# Reciprocal identities and scaled equations

Terms, Steps and Libraries use the representations in `prover/sig/proof.md`
and `prover/sig/library.md`. `premises` is a list of Steps in premise order.
The routines below return `(cons value lib)` with the Library after any
auxiliary lemmas have been added. A failure can occupy the value field.

| ACL2 call | Value |
|---|---|

Each Step recipe in the table also has a `-with-replies` form taking a
final reply alist. Value fields can contain a request of the form
`(:call kind lib . args)`, as in `prover/t4/sig/algebra.md`. To handle it,
associate the full request with the corresponding `(cons value lib)`
reply and repeat the initial call with the extended alist.
`t4-field-field-identity-with-replies` requests `:arithmetic` after it
recognizes an equality. In this form, the caller starts with the current
Library and processes arithmetic initialization like the other requests.
