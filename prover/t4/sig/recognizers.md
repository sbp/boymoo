# Recognizers

A Library and a Step use the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. A formula is a term in the form given there.
`recursive` is the set of recursive function symbols represented by a
list in the order of their S-expression text. Only membership is used.

| Call | Result | Failure |
|---|---|---|

`(t4-recognizers-recognizer-implication-with-replies lib formula recursive replies)`
uses the caller's implementation of `prove`. Start with empty replies.
A request has the form `(:t4-request :prove (term evidence definitions) lib)`.
Evaluate the requested method and append its `(cons step lib)` result
or failure to the replies, then repeat the call with its original
arguments. Evidence and definitions retain their supplied order.
The completed result has the same form as the Library-returning call.
