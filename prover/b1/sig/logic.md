# Proof-producing rewriting

A BookProof is a shared Library, in the form in `prover/sig/library.md`,
used with B1 rewriting and inference. B1 constant folding is provided by
`b1-logic-bookproof-constant`.
Terms, facts, binding pairs and Steps use the forms in `prover/sig/proof.md`.

The constants are `*b1-logic-symbolp*`, `*b1-logic-stringp*`,
`*b1-logic-symbol-name*`, `*b1-logic-symbol-package*`, `*b1-logic-atom*`,
`*b1-logic-endp*`, `*b1-logic-eql*`, `*b1-logic-eq*`,
`*b1-logic-return-last*`, `*b1-logic-zp*` and `*b1-logic-the-check*`.

The failure kinds appear in `prover/b1/notes/failures.md`. Normalization
entry points that return a Library can also return a branch result
carrying the test to be split. A step-only call returns a generic failure
when it encounters a branch request.

| Call | Result | Failure |
|---|---|---|
| `(b1-logic-match pattern term bindings)` | `(cons matched-p bindings)`. The alist is in insertion order and includes bindings made before a mismatch. | A malformed term can return a failure. |
| `(b1-logic-matching-claim claims goal)` | Name of the first matching unconditional candidate, or `nil`. The argument `claims` is the claims table of the search index. | A failure for a malformed term. |
| `(b1-logic-equal-to equality)` | A local rule that gives the equality Step when the term is its left side. | None when making the rule. |
| `(b1-logic-rational-value value)` | The ACL2 rational from an integer or ratio datum, or `nil`. | A failure for a malformed ratio or empty list. |
| `(b1-logic-rational-datum value)` | The integer or `("ratio" numerator denominator)` datum for the ACL2 rational `value`. | A value without rational fields can return a failure. |
| `(b1-logic-bookproof-from-fact lib name claim)` | The named fact instantiated to match `claim`. | `Unproved` if the fact does not match, or a proof failure. |
| `(b1-logic-bookproof-rewrite-rule lib name)` | A local rule from the left side of the named fact to its right. | A proof failure. |
| `(b1-logic-apply-rule lib rule term)` | Apply an equality or named fact rule to the term, giving a Step or `nil`. | A proof failure. |
| `(b1-logic-bookproof-prove-implication-premise lib formula)` | The assumed premise Step for proving the consequence. | A proof failure. |
| `(b1-logic-bookproof-prove-implication lib formula consequence)` | The discharged implication using the supplied consequence Step. | A proof failure or `RuleInapplicable` if the consequence concludes a different formula. |
| `(b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)` | The discharged implication using the supplied premise and consequence Steps. Use this to keep the premise when proving the consequence extends the Library. | A proof failure or `RuleInapplicable` if the consequence concludes a different formula. |
| `(b1-logic-bookproof-split-conjuncts lib step)` | The list of Steps for the conjuncts in left-to-right order. | A proof failure. |
| `(b1-logic-bookproof-contradiction lib positive negative goal)` | The cut of the two Steps with `goal` at the front of its clause. | A proof failure. |
| `(b1-logic-bookproof-forces lib goal assertion evidence unfold rules)` | A Step deriving `goal` by reducing the assertion to NIL under the opposite hypothesis. | `Unproved` or a proof failure. |
| `(b1-logic-bookproof-select-equivalent-test lib term equivalence)` | `(cons step lib)` for the equation replacing the IF test, with the auxiliary lemma installed if needed. | A proof failure or failed assertion. |
| `(b1-logic-bookproof-case-proof lib goal evidence unfold rules depth)` | A Step from normalization and cases. The default case depth is 16. | `Unproved`, `Fuel` or a proof failure. |
| `(b1-logic-bookproof-normalize-proof lib goal evidence unfold rules split)` | A Step proving `goal` by normalization or from evidence. | `Unproved`, `Fuel`, or a proof failure. |
| `(b1-logic-bookproof-normalize lib term evidence unfold rules split condition inspect-branches)` | The equality Step from left-to-right normalization of `term`. | `Fuel` or a proof failure. |
| `(b1-logic-bookproof-true-constant lib term)` | A proof of an established non-NIL quoted constant. | A proof failure. |
| `(b1-logic-bookproof-false-value lib negative)` | The equation to quoted NIL from a negation Step. | A proof failure. |
| `(b1-logic-bookproof-boolean-value lib step boolean)` | The equation to quoted T from a term Step and a Step that the term is Boolean. | A proof failure. |
| `(b1-logic-bookproof-equality-true lib step)` | The equation to quoted T from an equality Step. | A proof failure. |
| `(b1-logic-bookproof-constant lib term)` | The B1 constant-folding Step or `nil`. | A proof failure or a malformed-input failure. |

The claims table maps `(head first-argument-head)` to lists of rules in
insertion order. In the alist returned by `b1-search-fact-index-claims`,
the records have the form `(:b1-rule name term path)`. The general key
uses `:none` for an absent or noncompound first argument. A compound
first argument can have an empty head, represented by `nil`. An alist of
`(:rule name term path)` records uses `nil` in its general key. Search
tries the exact candidates from newest to oldest, followed by the general
candidates in the same order. An unconditional record has an empty `path`.

## Normalization callbacks

`evidence` is an ordered list of Steps, `unfold` is a list of definition
names used as a set for membership, and `rules` is a list of local rules
in their application order. All three default to `nil`. `split` and
`inspect-branches` default to `nil`. The `condition` argument defaults
to `nil`. A local rule from `equal-to` or `rewrite-rule` is evaluated
by the book. Represent any other rule or a condition function as
`(:callback id)`, where `id` identifies the caller's function and
can carry its arguments.

Each of `normalize`, `normalize-proof`, `case-proof` and `forces`
has a `b1-logic-bookproof-…-with-library` entry point with the same
arguments and a final `replies` argument, initially `nil`. It returns
`(cons step lib)` on success, a failure on error, or a request when a
callback is needed. Callers using their own callbacks use these entry
points. Each reply is `(cons step lib)` with the callback's resulting
Library and a Step or `nil`. A callback failure is also a reply. To
supply a reply, repeat the original call with the reply appended in
invocation order.

`b1-logic-call-p` recognizes requests. The accessors
`b1-logic-call-kind`, `b1-logic-call-id`, `b1-logic-call-library` and
`b1-logic-call-term` return the callback kind (`:rule` or
`:condition`), the callback identifier, the current Library and the
term. `b1-logic-branch-p` recognizes a branch result. Its accessors
`b1-logic-branch-test` and `b1-logic-branch-library` give the test and
the Library at the split. Each recognizer and accessor takes the result
as its only argument.

Use `(b1-logic-make-branch test lib)` as a callback reply to request a
split on `test` with the current Library `lib`.

`(b1-logic-bookproof-split-conjuncts-first lib step)` returns the first
conjunct Step or a failure.

`b1-logic-rational-value` accepts `:none` for an absent datum.

`(b1-logic-proof-not-nil proof)` takes a Proof and returns the Step
establishing that quoted NIL is false. It uses the ground Step when
the relevant premises match the ground theory. The general proof is
constructed by `proof-proof-not-nil`.
