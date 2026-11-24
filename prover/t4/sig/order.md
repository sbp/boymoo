# Strict orders

The Library, terms, and Steps follow `prover/sig/library.md` and
`prover/sig/proof.md`. Facts are searched in insertion order.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t4-order-strict-equation lib relation)` | `relation` is a term. Return its unfolded equality Step when its definition is the conjunction of an order test and unequal endpoints, or `nil`. | From unfolding or reading the definition, or `Fuel` when unfolding exhausts its allowance. |
| `(t4-order-strict-order lib claim replies)` | `claim` is a term. Return `(cons step lib)` with the proof of an applicable strict order law, or with `nil` as the Step if the recipe is inapplicable. The Library is the one resulting from the proof operations. | From a query or proof operation, or a failure for a different strict order or a missing order law. |

`strict-order` can return a request `(:t4-order-request operation arguments lib)`.
`t4-order-request-p` recognizes it, and `t4-order-request-operation`,
`t4-order-request-arguments`, and `t4-order-request-library` return its
fields. Start with `nil` replies, append the answer to each request, and
repeat the call with its original Library and claim. A failure reply is the
result of the entire call.

The operation `:fact-proof` has arguments `(formula premises)`. The
premises are a list of Steps in order for a fresh Evidence object. Its reply
is `(cons step lib)` with the resulting Library and with `nil` when the
fact proof is missing. The operation `:match` has arguments `(pattern term)`
and asks for a match with an empty bindings dictionary. Its reply is
`(cons matched-p bindings)` with the resulting ordered binding alist.

`(t4-order-imply lib antecedent consequent)` is the inference used to
introduce an implication. The antecedent is a term and the consequent is
a Step. It returns a Step or a failure.

The operation `:prove` takes `(term evidence definitions)`, where
`evidence` is a list of Steps and `definitions` is a list of symbols to
unfold. Its reply is `(cons step lib)` with the resulting Library.
