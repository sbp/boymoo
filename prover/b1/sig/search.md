# Proof search

Terms and Steps use the forms in `prover/sig/proof.md`. `lib` is a Library as in `prover/sig/library.md`. Evidence is an ordered list of Steps. `known` is an insertion-ordered alist from terms to Steps. `bindings` is an insertion-ordered alist from variables to terms.

A Rule has the form `(:b1-rule name term path)`. The path contains `"implies"` and the integers `0` and `1`, in the order in which the proof descends. `b1-search-make-rule` takes the three fields in that order. `b1-search-rule-name`, `b1-search-rule-term` and `b1-search-rule-path` take a Rule and return its indicated field.

A FactIndex has the form `(:b1-fact-index claims equations)`. Each index is an alist mapping `(head argument-head)` to a list of Rules. Keys and their Rule lists are in first-insertion order. The head of an absent or noncompound first argument is `:none`. An empty compound head is represented by `nil`. `b1-search-fact-index-claims` and `b1-search-fact-index-equations` take a FactIndex and return its indicated index.

An Attempt has the form `(:b1-attempt lib facts fuel definitions case-context)`. `facts` is a FactIndex. `fuel` is the remaining case and rewrite budget. `definitions` is the list of definitions available for unfolding, ordered by the text of their ACL2 forms. `case-context` is a Boolean. Each of `b1-search-attempt-lib`, `b1-search-attempt-facts`, `b1-search-attempt-fuel`, `b1-search-attempt-definitions` and `b1-search-attempt-case-context` takes one Attempt and returns its field. `b1-search-attempt-with-lib` takes an Attempt and a Library and replaces the Library.

The constants are `*b1-search-iff*` and `*b1-search-small-definitions*`. The second is a list representing a set in the same order as the Attempt's definitions field.

A result written `(cons value attempt)` or `(cons value lib)` can carry a failure in `value`. The Attempt or Library records changes made up to that point, including spent search budget and any auxiliary lemmas. `prover/b1/notes/failures.md` describes the failure kinds. An absent Step is `nil`.

| Function | Arguments in order | Result and failure conditions |
|---|---|---|
| `b1-search-subterms` | `term` | The list of terms in traversal order, including `term`. |
| `b1-search-key` | `term` | The two-element index key described above. Can return a failure for invalid indexing. |
| `b1-search-rule-proof` | Rule, `lib`, `bindings`, condition replies | A Step, a failure, or `(:request term)`. Replies are an alist from condition terms to Steps or failures. An absent reply produces a request for that term. |
| `b1-search-fact-index-init` | `lib` | The index built by visiting the library's facts in insertion order, omitting definitions. Can return a failure. |
| `b1-search-fact-index-add` | FactIndex, `name`, `clause` | The updated index. Can return a failure. |
| `b1-search-fact-index-candidates` | One index alist, `term` | The matching Rules from the exact bucket followed by the general bucket. Each bucket is visited from newest to oldest. Can return a failure. |
| `b1-search-attempt-init` | `lib`, FactIndex, `fuel`, `definitions`, `case-context` | An Attempt. The automatic search starts with fuel `65`. |
| `b1-search-attempt-charge` | Attempt | `(cons value attempt)` with `nil` or `SearchBudgetExhausted` in the value position. |
| `b1-search-attempt-evidence` | Attempt, `proofs`, `addition` | The expanded evidence list in order. Can return a failure. |
| `b1-search-attempt-establish` | Attempt, `term`, `known`, `depth` | `(cons value attempt)` with a Step or failure. |
| `b1-search-attempt-selector-formal` | Attempt, operator symbol | The one-based selector position, or `nil`. Can return a failure. |
| `b1-search-attempt-can-open` | Attempt, `term`, `known` | Boolean. Can return a failure. |
| `b1-search-attempt-boolean-type` | Attempt, `term` | `(cons value attempt)` with an optional Step or failure. |
| `b1-search-attempt-boolean-truth` | Attempt, `term`, `known` | `(cons value attempt)` with an optional Step or failure. |
| `b1-search-attempt-rewriting` | Attempt, `known` | A rewrite callback descriptor for the given known-evidence table. |
| `b1-search-attempt-rewrite-test` | Attempt, `conditional`, `known` | `(cons value attempt)` with an optional Step or failure. |
| `b1-search-attempt-structural-rule` | Attempt, `known` | A structural callback descriptor for the given known-evidence table. |
| `b1-search-attempt-apply-rule` | Attempt, callback descriptor, `term` | `(cons value attempt)` with an optional Step or failure for either search descriptor. |
| `b1-search-attempt-truth-of-cons` | Attempt, `term`, `known` | An optional Step or a failure. |
| `b1-search-attempt-condition` | Attempt, `term`, `known` | `(cons value attempt)` with an optional Step or failure. |
| `b1-search-attempt-normalize-evidence` | Attempt, `known` | `(cons value attempt)` with the updated known-evidence table or a failure. |
| `b1-search-attempt-local-rules` | Attempt, induction evidence, `known` | `(cons value attempt)` with `(rules known)` or a failure. The rules are in evidence order, and the returned map includes the added hypotheses. |
| `b1-search-attempt-examine-hypotheses` | Attempt, `formula`, `known`, `rules` | `(cons value attempt)` with `(optional-step known)` or a failure. |
| `b1-search-attempt-prove` | Attempt, `formula`, `evidence`, induction evidence, `depth` | `(cons value attempt)` with a Step or a failure. The automatic search starts at depth `3`. |
| `b1-search-attempt-with-cases` | Attempt, `formula`, `evidence`, induction evidence, `depth`, `test` | `(cons value attempt)` with a Step or failure. |
| `b1-search-attempt-anchors` | Attempt, `formula` | The candidate variables in traversal order. Can return a failure. |
| `b1-search-attempt-substitutions` | Attempt, `formula`, `variable` | The candidate substitutions in traversal order, each a list of two-element `(variable replacement)` lists. Can return a failure. |
| `b1-search-immediate-definitions` | `lib`, `formula` | The operator symbols in traversal order. Can return a failure. |
| `b1-search-automatic` | `lib`, FactIndex, `formula` | `(cons value lib)` with a Step or failure. |
| `b1-search-case-induction` | `lib`, FactIndex, `formula`, anchors | `(cons value lib)` with a Step or failure. |
| `b1-search-case-on-cons` | `lib`, FactIndex, `formula`, `variable`, `cons`, `hypothesis` | `(cons value lib)` with a Step or failure. |

`(b1-search-attempt-normalize attempt term evidence unfold rules split condition inspect-branches)` returns `(cons value attempt)` with a Step or a failure. Its arguments after `attempt` follow `b1-logic-bookproof-normalize`. Search rule descriptors can appear in `rules` alongside the ordinary normalization rules. Use `(list :b1-search-condition known)` to request proof of a condition from the known-evidence table, or `nil` for an absent condition. Calls to these descriptors carry the current Attempt.

`(b1-search-fact-index-logic-claims index)` supplies the claims table for `b1-logic-matching-claim` in bucket and rule order. It uses `:none` for the absent argument head and `nil` for an empty compound head. The rule descriptor `(list :b1-search-equivalent-test test equivalence)` uses `b1-logic-bookproof-select-equivalent-test` to rewrite an `IF` whose test equals `test`.

`(b1-search-make-fact-index claims equations)` constructs a FactIndex from its two ordered index alists.

`(b1-search-record-first-evidence known term step)` inserts the Step at `term` when its key is absent and returns the known-evidence alist.
