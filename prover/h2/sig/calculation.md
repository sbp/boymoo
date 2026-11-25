# Numeric calculation

Terms and Steps follow `prover/sig/proof.md`. A `library` is the shared
Library, `proof` is the H2 proof search object that contains a Library, and
`context` is the H2 search Context with its ordered literal map.

`h2-calculation-number-sums-init` takes a Library and returns
`(:h2-number-sums library)`, the representation of a NumberSums object.
`h2-calculation-number-sums-proof` returns its Library.
The `sums` argument in the table is a NumberSums object. Omitted evidence
is `nil`. Evidence Steps stay in the order supplied.

| Function | Arguments in order | Result |
|---|---|---|
| `h2-calculation-number-sums-cite` | Sums, lemma name string, list of actual terms, evidence Steps | Instantiated lemma Step, using the numeric lemma for each of the four signed-sum rules. |
| `h2-calculation-number-sums-type-of` | Sums, term, evidence Steps | Step proving ACL2-number membership. |
| `h2-calculation-number-sums-push-minus` | Sums, term, evidence Steps | Step for minus distribution or double negation, or `nil` if unchanged. |
| `h2-calculation-number-sums-linear-form` | Sums, term, evidence Steps | Equality Step to the right-associated sorted sum. |
| `h2-calculation-number-sums-linear-equal` | Sums, left term, right term, evidence Steps | Equality Step for the two terms. |
| `h2-calculation-number-sums` | Library | Updated Library, with signed-sum lemmas added in order if absent. |
| `h2-calculation-normalize-total-sum` | Library, term, projection rule names, sums | Equality Step to the sum with numeric fixes exposed. |

The constants are `*h2-calculation-numberp*`, `*h2-calculation-fix*`,
`*h2-calculation-reciprocal*`, `*h2-calculation-rationalp*` and
`*h2-calculation-number-rules*`. The rule names retain their declaration order.

`product-form` and `calculate` have entry points with `-with-replies` appended
to their names and an extra final reply list argument. The short entry points
begin with `nil` replies. A call that needs a BookProof operation returns
`(:h2-calculation-request operation proof context arguments)`.
`h2-calculation-request-p` recognizes it. The accessors have the same prefix
and the suffixes `-operation`, `-proof`, `-context`, and `-arguments`.
The operation is `:deduce` with `(term active)`, `:primitive` with `(term)`,
or `:spend` with no arguments. Each reply has the result form
`(cons step (cons proof context))`, with `nil` for the value of `:spend`.
Append the reply to the ordered list and call again with the original
arguments. Keep the enclosing BookProof state between requests.

`projected-arithmetic`, `equal-total-sums`, and `signed-identity` also have
`-with-replies` entry points with an additional final reply list argument.
They use the derivation request and reply interface under `alist-recognizers`
for the negation projection rule. A pending operation has the request in
the value position of `(cons value proof)`.

A delegated bound Library method has the form
`(:h2-number-sums-bound-method name library)`. The sum normalizer calls the Library proof operations directly.
