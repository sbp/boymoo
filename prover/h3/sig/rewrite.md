# Equational and propositional search

`lib` is a Library as specified in the shared Library signature.
Proof operations use its Proof. Terms and Steps use the shared Proof
signature. `evidence` is an insertion-ordered association list with
`(term . step)` entries. `bindings` is an insertion-ordered alist with
`(variable . term)` entries. `active`, `calls` and `definitions` are
sets represented as lists without repeats. Membership alone is observed
for these sets. The constructor retains first occurrence order.
`tests` is a list of tests in the order recorded, with repeats retained.

A Rules object is `(:h3-rules lib propositions equations)`. Each index
is an insertion-ordered alist from a head (possibly `nil`) to a list
of `(pattern fact)` pairs in the order the facts were supplied. Use
`h3-rewrite-rules-lib`, `h3-rewrite-rules-propositions` and
`h3-rewrite-rules-equations` to read the respective fields.

A Search is `(:h3-search lib definitions calls rules budget deep book)`.
`budget` is the remaining case budget as an integer, `deep` is a
Boolean, and `book` is `nil` for a search without book options. Use
`h3-rewrite-search-lib`, `h3-rewrite-search-definitions`,
`h3-rewrite-search-calls`, `h3-rewrite-search-rules`,
`h3-rewrite-search-budget` and `h3-rewrite-search-deep` to read the
respective fields. `h3-rewrite-search-with-lib` takes a Search and a
replacement Library for that Search.

Search calls returning a Search preserve the state reached even when the
value is a failure. Use the returned Search on the next call to the same
object. Calls returning tests likewise preserve any tests appended before
a failure. Passing `nil` supplies an empty active set, evidence alist, test
list, or list of original proof Steps.

The constants `*h3-rewrite-characterp*`, `*h3-rewrite-symbolp*`,
`*h3-rewrite-stringp*`, `*h3-rewrite-reciprocal*`,
`*h3-rewrite-return-last*` and `*h3-rewrite-closed-definitions*`
are the corresponding prover symbols and the set of closed definitions.

| ACL2 call | Result |
|---|---|
| `*h3-rewrite-unproved*` | `(:failure "unproved" "")` when a tactic runs out of proof options. |
| `(h3-rewrite-unproved-p value)` | Whether `value` is an `unproved` failure. |
| `(h3-rewrite-arguments term)` | The arguments of an unquoted compound term, or `nil`. Does not produce a failure. |
| `(h3-rewrite-match pattern term bindings)` | `(cons matched-p bindings)`, retaining bindings made before a failed match, or a failure. |
| `(h3-rewrite-implication lib antecedent result)` | The implication Step with `antecedent` discharged in the positive case, or a failure. `result` is a Step for its conclusion. |
| `(h3-rewrite-apply-implication lib proof guard)` | The consequence Step, using the implication Step and guard Step, or a failure. |
| `(h3-rewrite-nil-value lib negative)` | The Step equating the negated term in `negative` to quoted nil, or a failure. |
| `(h3-rewrite-negation lib equality)` | The negation Step from an equality to quoted nil, or a failure. |
| `(h3-rewrite-double-negation lib proof)` | The Step eliminating two negations, or a failure. |
| `(h3-rewrite-introduce-double-negation lib proof)` | The Step introducing two negations, or a failure. |
| `(h3-rewrite-nonnil-from-type lib proof)` | A Step for the argument of a recognizer that is false on nil, or a failure. |
| `(h3-rewrite-head-of term)` | The head of a compound term, or `nil` for an atom. May fail for an empty application. |
| `(h3-rewrite-encode-rational value)` | An integer or tagged ratio datum for the ACL2 rational `value`. Does not produce a failure on rationals. |
| `(h3-rewrite-rational-value value)` | An ACL2 rational for a rational datum, `nil` for a different kind of datum, or a failure. |
| `(h3-rewrite-primitive lib call)` | A primitive computation Step, `nil` when no computation applies, or a failure. |
| `(h3-rewrite-rules-init lib names transparent)` | Rules indexed from fact names in order, using the given transparent definitions, or a failure. Both lists default to `nil`. |
| `(h3-rewrite-search-init lib definitions calls rules budget deep)` | A Search. The defaults after `lib` are `nil nil nil 150 nil`. Does not produce a failure. |
| `(h3-rewrite-search-add-evidence search evidence proof)` | The evidence alist with the Step and its derived evidence entered, or a failure. |
| `(h3-rewrite-search-context search proofs)` | An evidence alist made from the ordered list of original Steps, or a failure. |
| `(h3-rewrite-search-known search term evidence)` | The known Step, `nil`, or a failure. |
| `(h3-rewrite-search-should-unfold search term)` | Whether the call can be opened, or a failure. |
| `(h3-rewrite-search-evaluate search term)` | A primitive computation Step, `nil`, or a failure. |
| `(h3-rewrite-search-visit-term search)` | `(cons value search)`; the value is `nil` or a failure. |
| `(h3-rewrite-search-rewrite-atom search value evidence)` | An atom rewrite Step, `nil`, or a failure. |
| `(h3-rewrite-search-arguments-first search term)` | Whether to rewrite the call's arguments first. Does not produce a failure. |
| `(h3-rewrite-search-reduce search term evidence tests active)` | `(list value search tests)` with a normalization Step, `nil`, or a failure as `value`. |
| `(h3-rewrite-search-derive search term evidence active tests)` | `(list value search tests)` with a Step or failure as `value`. |
| `(h3-rewrite-search-prove search term hypotheses)` | `(cons value search)` with a Step or failure as `value`. `hypotheses` is a list of original Steps. |

For a search with book options, call
`(h3-rewrite-search-with-book-options search inference-budget inside-first)`
on a Search. This initializes inference, normalization, and visit
budgets. Recursive calls use the book options and retain the remaining
budgets in the resulting Search. The ordinary case budget for a book
search is 14 and the ordinary inference budget is 130.

With book options, the `book` field is
`(inferences reductions visits inside-first)`. The first three fields
are remaining budgets and the last is a Boolean. A Library replacement
also updates the Rules Library when the two share a Library. The
closed definitions are stored in declared order. Searches check
membership in that set.
