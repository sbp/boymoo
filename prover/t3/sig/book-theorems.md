# Theorem search

Terms, Steps, and library proof data use the forms in `prover/sig/proof.md`.
`lib` is the book proof context. An absent term, a missing Step, and a
false Boolean use `nil`. A Step can establish the quoted NIL term.

A Context has the form
`(:t3-book-theorems-context lib facts equalities projections rewrites contradiction frozen)`.
Its four maps are insertion-ordered alists. The facts and equalities map a
term to a Step. Each value in projections or rewrites is a list of
`(step path guards)` recipes in the order recorded. Contradiction is a
Step or `nil`. Frozen is a set of terms represented by a list.

A theorem search has the form
`(:t3-book-theorems-theorems lib constructor-cases index rewrites fuel)`.
Its index and rewrites are insertion-ordered alists keyed by rule keys.
Each value is a list of `(name term path guards required)` recipes in the
order indexed. Required is a set of terms represented by a list. The
constructor flag is Boolean, and fuel is the search allowance
remaining, or `:none` before it is assigned.

## Terms and recipes

| ACL2 call | Result |
|---|---|
| `(t3-book-theorems-head term)` | The operator of a compound term, or `nil`. |
| `(t3-book-theorems-fingerprint term)` | The same result with compound operators represented by the Common Lisp LAMBDA symbol. |
| `(t3-book-theorems-rule-key term)` | The pair of the operator fingerprint and the list of the first two argument fingerprints. |
| `(t3-book-theorems-candidates index term)` | The indexed recipes in the order of the applicable keys, then in insertion order within a key. |
| `(t3-book-theorems-terms term)` | All subterms in preorder, skipping quoted data and operator positions. |
| `(t3-book-theorems-variables term)` | A list of the distinct noncompound subterms. |
| `(t3-book-theorems-match pattern term bindings)` | `(cons matched-p bindings)` with the updated insertion-ordered map, including bindings made before a failed match. |
| `(t3-book-theorems-projections term path guards)` | The list of `(term path guards)` triples reachable by elimination in traversal order. Use `nil` for the default path and guard list. |
| `(t3-book-theorems-conjuncts term)` | The leaf conjuncts in left-to-right order. |
| `(t3-book-theorems-project lib step path guards)` | Step obtained by following the path using the ordered guard Steps. |
| `(t3-book-theorems-recurrences name formals body)` | Recursive Calls in the order of `termination-recursive-calls`. |
| `(t3-book-theorems-drivers name formals body)` | The distinct one-based indices of the arguments changed by recursive calls, in ascending order. |
| `(t3-book-theorems-pending-test term)` | First pending conditional test, or `nil`. |
| `(t3-book-theorems-term-cost term limit)` | Cost of the traversal, ending after the first term that brings the cost above `limit`. Pass 1000 for the standard limit. |

These functions can return a failure from a malformed term, from proof
construction, or from exhaustion of recursion fuel. Set-valued results
are ordered by the text from `t3-book-theorems-sexp-text`.

## Context and search entry points

| ACL2 call | Result |
|---|---|
| `(t3-book-theorems-context-init lib frozen)` | Context with empty maps, no contradiction, and the given frozen terms. Pass `nil` for the default. |
| `(t3-book-theorems-context-lib context)` | The library. |
| `(t3-book-theorems-context-facts context)` | Context facts in insertion order. |
| `(t3-book-theorems-context-equalities context)` | Context equality map. |
| `(t3-book-theorems-context-projections context)` | Context projection map. |
| `(t3-book-theorems-context-rewrites context)` | Context rewrite map. |
| `(t3-book-theorems-context-contradiction context)` | Contradiction Step or `nil`. |
| `(t3-book-theorems-context-frozen context)` | Frozen term set. |
| `(t3-book-theorems-context-branch context test holds)` | The branch context with the signed test recorded. |
| `(t3-book-theorems-context-note context step)` | The updated Context after recording the Step and its consequences. |
| `(t3-book-theorems-context-nil-value context term)` | Equality Step for a denied term, or `nil`. |
| `(t3-book-theorems-theorems-init lib)` | Search object initialized from the library. |
| `(t3-book-theorems-theorems-lib search)` | The library in the search object. |
| `(t3-book-theorems-theorems-with-lib search lib)` | Search with the supplied library and its existing indexes. Use after changing declarations in the library. |
| `(t3-book-theorems-theorems-fuel search)` | Remaining search allowance, or `:none`. |
| `(t3-book-theorems-theorems-with-fuel search allowance)` | Search with the supplied allowance. |
| `(t3-book-theorems-theorems-index-fact search name formula)` | Search with the fact indexed. |
| `(t3-book-theorems-theorems-add search kind data)` | Search with the theorem, axiom, or constraint facts in `data` indexed when applicable. |
| `(t3-book-theorems-theorems-quick search term context depth)` | `(cons step search)` with the updated search. The Step can be `nil`. Pass 1 for the default depth. |
| `(t3-book-theorems-theorems-prove search term context depth)` | `(cons step (cons search context))` with the updated search and context. Pass 12 for the default depth. |
| `(t3-book-theorems-theorems-theorem search name formula)` | `(cons entry search)` with the updated search and the `proof-proof-entry` result. |

A function that executes an inference or search can return a failure as
its entire result. The search uses `unsupported` when no tactic applies.

The `lib` field of the search is a book proof context with its package
declarations, as specified in `prover/t3/sig/book-values.md`. The `lib`
argument of `project` and the `lib` field of a Context are the underlying
Library from `prover/sig/library.md`. Context inference uses that Library's
Proof. Theorem search uses the book proof context for primitive computations
that consult package declarations.

When a caller works with the underlying Library, use
`(t3-book-theorems-library search)` to read it and
`(t3-book-theorems-with-library search library)` to replace it. These
operations leave the package declarations and indexes available to the
search.

A search prepared for a session has the form
`(:t3-book-theorems-prepared lib constructor-cases index rewrites fuel summaries)`.
Each summary contains the name, formals, body, recursive calls and
changing argument indices. A lookup uses the summary for those exact
formals and body. A stored failure is reported when the corresponding
summary is requested during search.

| ACL2 call | Result |
|---|---|
| `(t3-book-theorems-prepare-definitions search)` | The search with definition summaries for its underlying library. |
| `(t3-book-theorems-prepare-prefix-definitions search names)` | The prepared search with summaries for the named new definitions. An ordinary search is returned as supplied. |
