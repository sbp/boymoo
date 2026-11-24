# Recognizers

A Library and a Step use the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. A formula is a term in the form given there.
`recursive` is the set of recursive function symbols represented by a
list in the order of their S-expression text. Only membership is used.

| Call | Result | Failure |
|---|---|---|
| `(t4-recognizers-recognizer-implication lib formula recursive)` | Step for an implication between two unary recognizers that follow the same cdrs, or `nil` when the recognizers do not fit the rule. The Library has no resulting update. | A failure from reading the formula or constructing the proof. |
| `(t4-recognizers-recognizer-implication-branch-view equation positive lib shape)` | Equality Step for the selected branch of the unfolded definition Step `equation`. `shape` is the cons test on the input and `positive` gives the truth of the test. | A failure from constructing the proof. |

`(t4-recognizers-recognizer-implication-with-library lib formula recursive)`
returns `(cons step lib)` with the Library from the inherited proof
operations when an auxiliary lemma is added. The first element is
`nil` when the recognizers do not fit the rule. A failure is the entire
result.

`(t4-recognizers-recognizer-implication-with-replies lib formula recursive replies)`
uses the caller's implementation of `prove`. Start with empty replies.
A request has the form `(:t4-request :prove (term evidence definitions) lib)`.
Evaluate the requested method and append its `(cons step lib)` result
or failure to the replies, then repeat the call with its original
arguments. Evidence and definitions retain their supplied order.
The completed result has the same form as the Library-returning call.
