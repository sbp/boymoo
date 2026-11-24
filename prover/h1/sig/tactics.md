# Proof search

Terms, Steps, Proofs and Libraries have the forms in `prover/sig/proof.md`
and `prover/sig/library.md`. Tests are ordered lists of two-element lists
`(term holds)`. A table is an insertion-ordered association list with
entries `(key . value)`. A set is a list of distinct elements.
`h1-tactics-variables` orders variables by the text from
`h1-tactics-variable-text`. An exhausted tactic returns
`(:failure "Unproved" "")`.

The constants are `*h1-tactics-booleanp*`, `*h1-tactics-return-last*`,
`*h1-tactics-symbolp*`, `*h1-tactics-stringp*`, `*h1-tactics-characterp*`
and `*h1-tactics-translation*`. The last constant lists the definitions
given default openings, in opening-table order.

| Call | Result |
|---|---|
| `(h1-tactics-call-head term)` | The head of a nonempty compound term, or `:none` if the term has no call head. |
| `(h1-tactics-variables term)` | The set of variables of the term. |
| `(h1-tactics-subterms term)` | The list of subterms, with the term first and the argument subterms in traversal order. |
| `(h1-tactics-match pattern term free bindings)` | `(cons matched-p bindings)` with the resulting dictionary, including bindings made before an unsuccessful match. The set `free` lists the variables that can be bound. |

A Rule is `(:h1-rule step free)` with the Step and its set of free
variables. Rules is `(:h1-rules library claims rewrites)`. The Library
supplies the inference methods used when adding formulas. Each index
maps a term head to a list of `(pattern rule)` in order of addition.
An absent head uses the `:none` key.

| Call | Result |
|---|---|
| `(h1-tactics-rules-init prover)` | An empty Rules with the Prover's Library. |
| `(h1-tactics-rules-library rules)` | The Library used by Rules. |
| `(h1-tactics-rules-claims rules)` | The index of claims. |
| `(h1-tactics-rules-rewrites rules)` | The index of rewrites. |
| `(h1-tactics-rules-with-library rules library)` | Rules with the supplied Library. |
| `(h1-tactics-rules-add rules step general rewrite)` | Rules with the Step indexed. The flags `general` and `rewrite` default to `t`. |
| `(h1-tactics-rules-add-formula rules step general rewrite)` | Rules with the consequences of the formula indexed. The flags default to `t`. |

A Prover is `(:h1-prover library rules theorems schemas search-work case-limit)`.
`theorems` maps a formula to the name of its first registered theorem.
`schemas` maps a pair of heads to lists of `(name formula free)` in
registration order. A key with no secondary head has `:none` in its
second field. `search-work` is the initial rewriting work budget of
each Search, with `:none` for unbounded work. `case-limit` is `:none`
for a Prover and the bound on each proof's splits for a BookProver.
An integer `case-limit` selects the BookProver behavior for prior
facts, constant reduction and the bounds in `solve` and `by-induction`.

| Call | Result |
|---|---|
| `(h1-tactics-prover-init)` | A Prover initialized with the propositional lemmas and empty indexes. |
| `(h1-tactics-make-prover library rules theorems schemas search-work case-limit)` | A Prover with the supplied fields. |
| `(h1-tactics-prover-library prover)` | The Prover's Library, used for Library and propositional methods. |
| `(h1-tactics-prover-proof prover)` | The Proof in the Prover's Library, used for shared Proof methods. |
| `(h1-tactics-prover-rules prover)` | The Prover's Rules with its current Library. |
| `(h1-tactics-prover-theorems prover)`, `(h1-tactics-prover-schemas prover)`, `(h1-tactics-prover-search-work prover)`, `(h1-tactics-prover-case-limit prover)` | The named field. |
| `(h1-tactics-prover-with-library prover library)`, `(h1-tactics-prover-with-rules prover rules)`, `(h1-tactics-prover-with-theorems prover theorems)`, `(h1-tactics-prover-with-schemas prover schemas)`, `(h1-tactics-prover-with-search-work prover work)`, `(h1-tactics-prover-with-case-limit prover limit)` | Prover with the indicated field set. |
| `(h1-tactics-prover-prior-fact prover term)` | The Step for an earlier theorem or `nil`. |
| `(h1-tactics-prover-quoted-truth prover term)` | A Step proving the truth of a quoted non-NIL term. |
| `(h1-tactics-prover-false-equation prover evidence)` | The equality Step proving the value of the negated term is NIL, or `nil` when the evidence is absent. |
| `(h1-tactics-prover-equality-is-true prover evidence)` | The equality Step proving the value of the equality in the evidence is T. |
| `(h1-tactics-prover-conjunction-assumption prover term)` | A Step proving the conjunction under its conjuncts. |
| `(h1-tactics-prover-constant prover term)` | A Step for the constant computation or `nil`. |
| `(h1-tactics-prover-setup-rules prover)` | The Prover with its rules initialized. |
| `(h1-tactics-prover-solve prover formula openings limit)` | A Step proving the formula. |
| `(h1-tactics-prover-functions-in prover formula)` | Definition names in order of first occurrence in the formula, excluding translation names. |
| `(h1-tactics-prover-helper prover name step guards rewrite)` | `(cons step prover)` with the named helper Step and the Prover containing the entry, fact and rule. `name` is the label string, `guards` is a list of terms, and `rewrite` defaults to `t`. |
| `(h1-tactics-prover-by-induction prover formula measure substitutions openings ordinal limit assume-premise preserve split-on)` | The induction Step. Each substitution is `(bindings descent-step)` with bindings in argument order, each of the form `(formal actual)`. Pass `nil` for an omitted ordinality Step or `:none` for an omitted split term. |

A Search is `(:h1-search prover local ambient protected rewrite-equalities
openings remaining work)`. Its local Rules are searched before the
Prover's Rules. The ambient and protected fields are sets of terms.
The openings field is a dictionary from heads to their bounds, with the
translation heads installed first and existing positions retained on
update. An `openings` argument to a constructor, `solve` or
`by-induction` can also be a list of names, which assigns each name
bound 1. The default for openings, local Rules, ambient terms and
protected terms is `nil`. The default limit is 160 and the default
for `rewrite-equalities` and `assume-premise` is `nil`. The
`preserve` argument defaults to an empty term list.

A Context is `(:h1-context search tests evidence bindings active guards)`.
The evidence dictionary maps a term to its Step, or to `nil` for a
recorded unsuccessful lookup. The bindings dictionary maps a left side
to its equality Step. The active and guards fields are sets of terms.
The Search in the returned Context carries the work still available.
Pass that Search when reusing the same search with another Context.

| Call | Result |
|---|---|
| `(h1-tactics-search-init prover openings local ambient protected limit rewrite-equalities)` | A Search with the given options and the Prover's work budget. |
| `(h1-tactics-search-prover search)`, `(h1-tactics-search-local search)`, `(h1-tactics-search-ambient search)`, `(h1-tactics-search-protected search)`, `(h1-tactics-search-rewrite-equalities search)`, `(h1-tactics-search-openings search)`, `(h1-tactics-search-remaining search)`, `(h1-tactics-search-work search)` | The named field. |
| `(h1-tactics-search-with-work search work)` | Search with the given work budget. |
| `(h1-tactics-search-reduce search term context tests fuel depth)` | `(list step context tests)` with the reduction Step or `nil`, the resulting Context and the resulting dictionary of pending tests. That dictionary maps terms to `nil`. `fuel` is the dictionary of available openings and `depth` defaults to 0. |
| `(h1-tactics-search-prove search term tests split-and)` | `(cons step search)` with the proof Step and the resulting Search. The defaults are an empty list of tests and `t` for `split-and`. |
| `(h1-tactics-search-with-premise search formula)` | `(cons step search)` with the implication Step and the resulting Search. |
| `(h1-tactics-search-contradiction search context)` | `(cons step context)` with a contradiction Step or `nil`, and the resulting Context. |
| `(h1-tactics-context-init search tests)` | A Context with the given tests and their initial evidence. |
| `(h1-tactics-context-search context)`, `(h1-tactics-context-tests context)`, `(h1-tactics-context-evidence context)`, `(h1-tactics-context-bindings context)`, `(h1-tactics-context-active context)`, `(h1-tactics-context-guards context)` | The named field. |
| `(h1-tactics-context-with-search context search)`, `(h1-tactics-context-with-evidence context evidence)`, `(h1-tactics-context-with-bindings context bindings)` | Context with the indicated field set. |
| `(h1-tactics-context-bind-equality context step)` | Context with the equality binding recorded if applicable. |
| `(h1-tactics-context-select context term)` | `(cons step context)` with a branch-selection Step or `nil`, and the resulting Context. |
| `(h1-tactics-context-apply context index term)` | `(cons step context)` with the first applicable rule Step or `nil`, and the resulting Context. `index` is `"claims"` or `"rewrites"`. |
| `(h1-tactics-context-guard context term)`, `(h1-tactics-context-find context term)`, `(h1-tactics-context-derive context term)` | `(cons step context)` with the requested evidence Step or `nil`, and the resulting Context. |
| `(h1-tactics-context-learn context premise)` | Context with the results forced by the given premise. |
| `(h1-tactics-context-if-consequences context step)` | `(cons steps context)` with the list of consequence Steps and the resulting Context. |

The constructors, field accessors, field setters, term walks, pattern
matching and `functions-in` return their listed results on these inputs. Prover
and Context initialization, rule addition and the proof and search
operations can return a failure in place of the listed result.

## BookProver fields and methods

A BookProver may carry two fields after `case-limit`, a set of available
names and an insertion-ordered dictionary of evaluator equations. The
Prover setters retain these fields. An absent field reads as `nil`.

| Call | Result |
|---|---|
| `(h1-tactics-prover-available prover)`, `(h1-tactics-prover-evaluators prover)` | The named field. |
| `(h1-tactics-prover-with-available prover available)`, `(h1-tactics-prover-with-evaluators prover evaluators)` | Prover with the supplied field set. |
| `(h1-tactics-prover-add-definition prover name formals body)` | Prover with the named definition and its equation. A BookProver also records the name as available. |
| `(h1-tactics-prover-record-formula prover label step rewrite)` | `(cons fact prover)` with the named fact and the Prover containing its entry and index records. `label` is a string. `rewrite` is Boolean and defaults to `nil`. May return a failure. |
| `(h1-tactics-fact-key term)` | Two-element schema key. A missing head is `:none`. May return a failure on a malformed argument. |
| `(h1-tactics-rational-constant term)` | The ACL2 rational denoted by a quoted integer or ratio, or `nil`. May return a failure. |
| `(h1-tactics-compute-rational prover term)` | The constant-computation Step for a recognized call on quoted rationals, or `nil`. May return a failure. |
