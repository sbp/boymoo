# Structural descent

Terms, Steps and Libraries use the forms in `prover/sig/proof.md` and
`prover/sig/library.md`. `lib` is a Library. `Structural` inherits the
Library representation. `strict` is a Boolean. An optional `cons` or
`tail-cons` argument is a Step establishing `CONSP`, or `nil` when omitted.

An Evidence object has the form `(:t4-structural-evidence hypotheses expanded recorded)`.
`hypotheses` is the shared Hypotheses object, `expanded` is a Boolean, and
`recorded` lists distinct literals in the order they were first recorded.
The tests and the `extra` and `found` maps retain their original order.
The `extra` argument to the constructor is the list of Steps in source
order. A repeated literal keeps its position in the map and takes the
last Step supplied for it.

| Call | Result |
|---|---|
| `(t4-structural-count term)` | The term `(ACL2-COUNT term)`. |
| `(t4-structural-evidence-init lib tests extra)` | Evidence for the signed `(test holds)` pairs and the extra Steps. Pass `nil` for either omitted list. |
| `(t4-structural-evidence-hypotheses evidence)` | The underlying Hypotheses. |
| `(t4-structural-evidence-proof evidence)` | The Library or Proof held by the Evidence. |
| `(t4-structural-evidence-tests evidence)` | The signed tests in their original order. |
| `(t4-structural-evidence-extra evidence)` | The insertion-ordered alist from extra literals to Steps. |
| `(t4-structural-evidence-found evidence)` | The insertion-ordered alist from discovered literals to Steps. |
| `(t4-structural-evidence-expanded evidence)` | Whether expansion has begun. |
| `(t4-structural-evidence-recorded evidence)` | The distinct recorded literals. |
| `(t4-structural-evidence-with-proof evidence lib)` | The Evidence with the given Library or Proof. |
| `(t4-structural-evidence-find evidence term)` | `(cons step evidence)` with the resulting Evidence. The Step is `nil` if no proof was found. |
| `(t4-structural-evidence-require evidence term)` | The same pair as `find`, with a failure for a missing proof. |
| `(t4-structural-evidence-record evidence step)` | Evidence with the literal and its structural consequences recorded. |
| `(t4-structural-evidence-non-nil-selector literal)` | The selector application whose value is known to be non-nil, or `nil`. |

The Evidence constructor, queries, `record` and `non-nil-selector` can
return a failure. The constructor can return a failure when reading a Step or its
literal. The accessors, `with-proof`, and `count` do not return a failure.

The constants are `*t4-structural-atom*`, `*t4-structural-endp*`,
`*t4-structural-null*`, `*t4-structural-eq*`, `*t4-structural-eql*`,
`*t4-structural-accessor*`, `*t4-structural-last*`,
`*t4-structural-evens*`, `*t4-structural-odds*`,
`*t4-structural-tuple-tail*`, `*t4-structural-tuple-empty*`, and
`*t4-structural-test-definitions*`. The test definitions are a membership
set in declaration order.

## Structural methods

Each method can return a failure from term access or proof construction,
or from a failed check for the requested comparison. A failure is the
entire result. Successful Step-producing calls return `(cons step lib)`
with the resulting Library. Where the method also takes Evidence, the
successful result is `(list step lib evidence)` with both resulting
objects. `evens-weak-lemma` returns the resulting Library directly.

| Call | Step or effect |
|---|---|
| `(t4-structural-structural-comparison-chain lib left right)` | The composition of the two integer comparison Steps in their given order. It can add `WEAK-TRANSITIVE`. |
| `(t4-structural-structural-cons-count lib obj cons)` | The count equation for `obj` under the cons proof `cons`. |
| `(t4-structural-structural-constructor-count lib a b)` | The count equation for `(CONS a b)`. |
| `(t4-structural-structural-replace-endpoints lib step left right)` | The comparison `step` rewritten using the two endpoint equality Steps `left` and `right`. |
| `(t4-structural-structural-add-prefix lib step a)` | The comparison of the endpoints after adding the prefix `1 + a` to each. |
| `(t4-structural-structural-count-of-nil lib)` | The simplification equality for the count of quoted nil, or `nil` if unchanged. |
| `(t4-structural-structural-zero-bound lib parent cons)` | A weak lower bound of zero on the count of `parent`, or a strict bound with the cons Step. |
| `(t4-structural-structural-count-bound lib child parent evidence strict)` | The strict or weak comparison of the counts of `child` and `parent`. The proof may add a path or transformation lemma. |
| `(t4-structural-structural-last-bound lib obj)` | The weak count bound for `LAST` on `obj`. |
| `(t4-structural-structural-split-bound lib head obj tail-cons)` | The weak or strict count bound for the `EVENS` or `ODDS` operation on `obj`. |
| `(t4-structural-structural-evens-nonempty lib smaller cons nonempty)` | The count comparison from the recursive bound `smaller`, a cons Step, and an `ENDP` falsity Step. |
| `(t4-structural-structural-tuple-descent lib goal evidence)` | The ordinal comparison for a descent through a tuple tail. |
| `(t4-structural-structural-count-descent lib goal evidence)` | The ordinal comparison for a decrease in counts. |
| `(t4-structural-structural-sum-descent lib goal evidence)` | The ordinal comparison for a decrease in sums. |
| `(t4-structural-structural-numeric-descent lib child parent evidence)` | A strict integer comparison of the two size terms. |

For `branch-results`, pass `nil` for the initial `replies`. Each supplied
reply is `(cons step lib)` with the callback Step and Library, or a failure.
Replies are a list in callback order. If another reply is needed, the
result is `(cons (list :t4-structural-branch-results node) lib)`, with the
Library as of that callback. Call the leaf with `node` and that Library,
append its reply, and repeat with the original call arguments. The lemma
is available to the leaf. Visits are true branch first and false branch
second, with lambda applications opened at the visit site.

The same traversal can be resumed with
`(t4-structural-branch-results-start lib name value template)` and
`(t4-structural-branch-results-resume request reply)`. They return
`(cons step lib)`, `(cons request lib)`, or a failure.
`t4-structural-branch-request-p` recognizes the request and
`t4-structural-branch-request-node` returns its callback argument. The
resume operation takes that request and the callback reply from its
Library. It continues the traversal at that point.

`(t4-structural-direct-builtin lib clause evidence)` returns the
`(cons step evidence)` result of finding a built-in instance with
structural evidence, or a failure. `step` is `nil` when no instance applies.
Evidence lookups and the built-in operation also accept a shared
Hypotheses object and return that form in the result in that case.
