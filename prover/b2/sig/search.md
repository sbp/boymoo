# B2 proof search

Terms, Steps, and the Library use the shared representations in `prover/sig/`.
An evidence list holds Steps in the supplied order. A known-evidence
table is an association list of `(term . step)` entries in insertion
order.

| Call | Result |
|---|---|
| `(b2-search-terms term)` | Preorder list of the term and its argument subterms. Traversal visits arguments and treats quotations as leaves. An empty compound produces a failure. |
| `(b2-search-size term limit)` | Number of terms visited by the same traversal, capped at the integer limit. An empty compound produces a failure. |
| `(b2-search-head term)` | Head of a compound term, `:none` for an atomic term, or a failure for an empty compound. |
| `(b2-search-beta-predicate term)` | A two-element term for the predicate of a unary translated lambda application, or `nil`. May return a failure on a malformed lambda or compound. |
| `(b2-search-guards term)` | List of the guards of a conjunction, left before right. May return a failure on a malformed conditional. |
| `(b2-search-boolean-test term)` | The first exposed conditional test, or `:none`. May return a failure on a malformed compound or conditional. |
| `(b2-search-search-theorem lib formula)` | A proof Step for the formula. May return a failure, including `Unproved` when search fails. |

A Search object has the form `(:b2-search lib index equations beta-paths fuel rules path)`.
The constructor `(b2-search-search-init lib fuel rules)` takes a Library,
its integer inference budget and a list of rewrite Steps. It returns the
Search or a failure. The standard budget is `32` and `nil` supplies an
empty rewrite list.
The accessors `b2-search-search-lib`, `b2-search-search-index`,
`b2-search-search-equations`, `b2-search-search-beta-paths`,
`b2-search-search-fuel`, `b2-search-search-rules` and
`b2-search-search-path` each take a Search and return its named field.

The index and equations are association lists in first-key insertion order.
Each index bucket holds `(name formula)` rows in fact order, and each
equations bucket holds `(name formula pattern)` rows in the same order.
`beta-paths` maps fact names to rewrite places in insertion order.
`path` is the stack of active `(goal keys)` requests, most recent first.
Each `keys` list is compared as a set of known terms.

`(b2-search-search-with-lib search lib)` replaces the Search's Library.
Fact buckets come from the Library supplied at initialization. Lookup
of an indexed fact uses the current Library.

`prove`, `infer` and `fact` return `(cons value search)`.
Their value field holds a Step, `nil` for a failed fact lookup, or a failure.
The state field holds the remaining inference budget. Thread it through
successive calls on the same Search. `b2-search-search-prove` restores
the caller's stack before returning. Pass `nil` for an empty evidence
list and `3` for each of the standard depth and split limits.

| Call | Result |
|---|---|
| `(b2-search-search-prove search goal evidence depth splits)` | Search for a proof of the goal, with its updated budget. May return a failure in the value field. |
| `(b2-search-search-infer search goal evidence known depth splits)` | Try inferences on the goal using the supplied evidence and known table, with the updated budget. May return a failure in the value field. |
| `(b2-search-search-fact search goal known depth splits)` | First matching fact Step provable within the limits, or `nil`, with the updated budget. May return a failure in the value field. |
| `(b2-search-search-short-definition search function)` | Whether the function has a definition of fewer than 85 terms. May return a failure on a malformed body. |
| `(b2-search-search-options search goal)` | List of `(definitions branches)` pairs in generation order. The definition lists preserve first occurrence, and branches is Boolean. May return a failure on malformed data. |
| `(b2-search-search-extend search premise)` | List of the premise Step followed by its derived Steps. May return a failure from proof construction. |
| `(b2-search-search-bindings search pattern goal formula known)` | Binding table in match order, or `:none` when matching fails. An absent implication formula can be passed as `nil`. May return a failure on malformed data. |
| `(b2-search-search-rewrite-test search goal evidence known)` | First proof found by rewriting one side of the equality goal, or `nil`. May return a failure from proof construction. |
| `(b2-search-search-arithmetic search goal known)` | An arithmetic proof Step, or `nil`. May return a failure from proof construction. |
| `(b2-search-search-reduce search goal evidence)` | List of the normalization results in traversal order, including `nil` results. May return a failure from normalization. |
| `(b2-search-search-substitute-equal search goal evidence known)` | First proof found using an established equality, or `nil`. May return a failure from proof construction. |

`*b2-search-wrappers*` is the set of wrapper symbols, ordered by the
text of their serialized forms for comparison.
