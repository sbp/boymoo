# Guarded induction

`lib` is a Library, and `ordinal` and decreases are Steps. Their forms
are specified in the shared Library and Proof signatures. A substitution
map is an insertion-ordered alist with entries `(variable . term)`.
`replacements` is a list of two-element lists in the supplied order.
Each is `(mapping decrease)` for well-founded induction, or
`(mapping reason)` for structural induction, where an integer reason
selects a built-in clause and any other reason is a decrease Step.

The `prove-case` argument is a list of callback replies in invocation
order. Each reply is a Step or failure. A call that reaches a case without
a supplied reply returns `(:request evidence)`, where `evidence` is the
ordered argument list of Steps for that case. The caller can add the reply
and repeat the original call. The case enumeration functions give all
callback arguments in order for a caller that can prepare them up front.
The guard walk visits a true branch before its false branch.

| ACL2 call | Result |
|---|---|
| `(h3-induction-well-founded lib formula measure ordinal replacements prove-case)` | The induction Step, a case request, or a failure. |
| `(h3-induction-structural-induction lib formula variable replacements prove-case)` | The induction Step using `ACL2-COUNT` of `variable`, a case request, or a failure. |
| `(h3-induction-request-p value)` | Whether `value` is a case request. Does not produce a failure. |
| `(h3-induction-request-evidence request)` | The evidence list of a case request. Does not produce a failure. |
