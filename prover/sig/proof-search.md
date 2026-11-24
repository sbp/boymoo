# Proof search

A term has the form specified in `prover/sig/proof.md`. A Library has the
form specified in `prover/sig/library.md`. Evidence is a list of Steps in
order. A known-evidence table is an alist with term keys and Step values
in insertion order. Bindings are likewise an alist from variables to terms,
with entries of the form `(variable . term)`.

A Rule is the record `(:rule name pattern expose)`, where `name` is
a fact name, `pattern` is a term, and `expose` is a Boolean. Use
`proof-search-rule-name`, `proof-search-rule-pattern`, and
`proof-search-rule-expose` to read its fields. Each takes a Rule.

A FactIndex is `(:fact-index lib rules equations)`. The two indexes are
alists from keys of the form `(head first-argument-head)` to lists of
Rules in insertion order. Use `proof-search-fact-index-lib`,
`proof-search-fact-index-rules`, and `proof-search-fact-index-equations`
to obtain these fields. Each takes a FactIndex. An absent bucket has the
value `nil`. Use `(proof-search-fact-index-with-lib index lib)` to
replace the Library after extending or copying it. Recursive invocations
are computed from the current Library definitions. The Rule and FactIndex
accessors and `with-lib` do not return a failure.

A Search is `(:search lib index budget rewriting logical pending)`.
`lib` is its Library, `index` is a FactIndex, `budget` is the remaining
number of calls to `proof-search-search-prove`, `rewriting` and `logical` are
Booleans, and `pending` is the set of active `(formula literals splits)`
triples, as a list. Use `proof-search-search-lib`,
`proof-search-search-index`, and `proof-search-search-budget` to read
the corresponding fields. Each takes a Search and does not return a failure.
After a call returning `(cons value search)`, use the returned Search
for the next call. Its Library contains any auxiliary lemmas made during
the call. The value can be a Step or a failure.

A `condition` argument is an alist of `(term . result)` entries, where
`result` is the Step or failure the condition function returns on that
term. Use `:none` when there is no condition function. If an alist lacks
a requested answer, the result is
`(:request term)`. Such a request can be answered by adding the entry
and calling again. `proof-search-request-p` tests that form, with the
requested term at `cadr`.

All listed arguments are explicit. The default arguments to
`proof-search-search-init` are `48 nil nil` after the Library and
FactIndex. The defaults after the formula in `proof-search-search-prove`
are `nil 2`.

| Function | Arguments in order | Result |
|---|---|---|
| `proof-search-head` | Term | The atomic operator, or `nil` for a variable or a lambda application. may return a failure for an empty application. |
| `proof-search-key` | Term | The pair `(head first-argument-head)`. The second field is `nil` except for the operators `EQUAL`, `NOT`, and `IMPLIES`. may return a failure for a malformed application. |
| `proof-search-conclusion` | Term | The term after opening leading lambdas and implications, or a failure. |
| `proof-search-can-shorten` | Term and size limit | Boolean saying whether the term or an `IF` branch is smaller than the limit. May return a failure. |
| `proof-search-conditional-test` | Term | The first conditional test in the traversal of the term, or `nil`. may return a failure for a malformed conditional. |
| `proof-search-fact-index-init` | Library | A FactIndex of the Library's facts, or a failure. |
| `proof-search-fact-index-add` | FactIndex, fact name | The FactIndex with that fact indexed, or a failure. The Library already contains the fact at that name. |
| `proof-search-fact-index-candidates` | FactIndex, goal term | The candidate Rules in search order, or a failure. |
| `proof-search-fact-index-apply` | FactIndex, Rule, bindings, condition | The specialized Step, a failure, or a condition request. |
| `proof-search-fact-index-prove` | FactIndex, goal term, condition | The matching fact Step, a failure, or a condition request. |
| `proof-search-fact-index-rewrite` | FactIndex, term, condition | The shortening equality Step, `nil`, a failure, or a condition request. |
| `proof-search-fact-index-recursive-invocations` | FactIndex, defined name | List of recursive calls in traversal order, or a failure. |
| `proof-search-fact-index-recursive-arguments` | FactIndex, defined name | List of recursive call argument lists, or a failure. |
| `proof-search-search-init` | Library, FactIndex, budget, rewriting Boolean, logical Boolean | A Search. |
| `proof-search-search-prove` | Search, formula, evidence, splits | `(cons value search)`, with a proof Step or a failure as the value. |
| `proof-search-search-premise` | Search, term, evidence, known-evidence table | `(cons value search)`, with a premise Step or a failure as the value. |
| `proof-search-induction-plans` | FactIndex, formula | Alist from variables to alists mapping substitution lists to selector terms, all in insertion order, or a failure. Each substitution list contains two-element `(variable replacement)` pairs. |
| `proof-search-logical-selector-goal` | Formula, variable | Boolean, or a failure from inspecting the conclusion. |
| `proof-search-prove-selector-induction` | Library, FactIndex, formula, induction plans, logical Boolean | `(cons value lib)`, with a proof Step or a failure as the value. |
| `proof-search-prove-theorem` | Library, FactIndex, formula | `(cons value lib)`, with a proof Step or a failure as the value. |

## Search operations

The following operations use the same Search, evidence and known-evidence
table as `proof-search-search-premise`.

| Function | Arguments in order | Result |
|---|---|---|
| `proof-search-search-with-lib` | Search, new Library | Search with the new Library. If the index had the Search's Library, the index also uses the new Library. |
| `proof-search-search-evidence` | Search, original evidence | The expanded evidence Steps in order, or a failure. |
| `proof-search-search-prove-premise` | Search, term, evidence, known-evidence table | The premise Step or failure paired with the Search. |
| `proof-search-search-computed-premise` | Search, term, known-evidence table | The optional computed Step or failure paired with the Search. |
| `proof-search-search-context-premise` | Search, term, evidence, known-evidence table | A Step or a failure. |
| `proof-search-search-search` | Search, formula, evidence, splits | The Step or failure paired with the Search. The entry itself spends no budget. Recursive calls to `proof-search-search-prove` spend budget. |
| `proof-search-search-logical-formula` | Search, formula, evidence, known-evidence table | The optional logical proof Step or failure paired with the Search. |
| `proof-search-search-fixed-arguments` | Search, left and right calls, argument position, before and after arguments, evidence, known-evidence table | The optional invariance Step or failure paired with the Search. |
| `proof-search-search-invariance` | Search, call, fixed call, fixed argument, position, condition | The optional invariance Step, failure or condition request paired with the Search. |
