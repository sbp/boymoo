# Reductions and induction instances

`lib` is a library in the form specified in `prover/sig/library.md`. A term
has the form specified in `prover/sig/proof.md`. `step`, `prefix`,
`evidence` when singular, and `descent` are proof steps. `active` is the
list of enclosing terms, in order from outermost to innermost, with `nil`
for an empty list. `book-logic-instance` and `book-logic-reducer-prove`
use the `Unproved` failure described in `prover/notes/failures.md`.

| ACL2 call | Result |
|---|---|
| `(book-logic-match pattern value bindings)` | `(cons matched bindings)`. The Boolean `matched` says whether `value` matches `pattern`. `bindings` is the insertion-ordered alist of variable bindings, including any made before a failed match. |
| `(book-logic-instance lib name formula)` | A step for the formula as an instance of a named fact, or a failure. |
| `(book-logic-term-size term limit)` | The size counted through the first node that exceeds the integer limit, or through the whole term. |
| `(book-logic-within-size term limit)` | Whether the integer size limit permits the term. |

## Reducer

The constructor takes a library, an ordered list of evidence steps, a
list of definition names permitted to unfold, a Boolean controlling
exposure of conditionals, an integer reduction budget, an integer size
limit, a rewrite callback, and a Boolean for logical reduction. Use
`nil` for empty evidence or definitions, `:none` for unrestricted
definitions, `800` and `400` for the default budget and size, and `nil`
for the default Booleans and rewrite callback.

The representation is `(:reducer lib evidence definitions expose budget
size rewrite logical memo)`. Evidence is keyed by the first literal of
each step. The memo associates `(term active)` with a step or `nil`.
Use the constructor and accessors to work with this object.

| ACL2 call | Result |
|---|---|
| `(book-logic-reducer-init lib evidence definitions expose budget size rewrite logical)` | A reducer, initially with an empty memo. |
| `(book-logic-reducer-lib reducer)` | Its library. |
| `(book-logic-reducer-known reducer term)` | A step proving a term directly from the evidence and axioms, `nil`, or a failure. |
| `(book-logic-reducer-disjoint reducer term)` | A step proving the negation of a term from incompatible types, `nil`, or a failure. |
| `(book-logic-reducer-reduce reducer term active)` | `(cons step reducer)` for the equality obtained by reduction. |
| `(book-logic-reducer-reduction reducer term active)` | `(cons step reducer)` for one reduction, without consulting or updating the memo for this term. |
| `(book-logic-reducer-truth-value reducer term)` | An equality step for a truth value, `nil`, or a failure. |
| `(book-logic-reducer-true-equality reducer term evidence)` | An equality step for a true Boolean term, or a failure. |
| `(book-logic-reducer-completion reducer term active)` | `(cons step reducer)` for application of a completion axiom. |
| `(book-logic-reducer-extend reducer prefix step)` | The equality formed by extending `prefix` with `step`, or a failure. |
| `(book-logic-reducer-may-open term active)` | Whether the term may be unfolded given its enclosing terms. |
| `(book-logic-reducer-conditional reducer term active)` | `(cons step reducer)` for conditional reduction. |
| `(book-logic-reducer-prove reducer term)` | `(cons step reducer)` for a proof of `term`. |
| `(book-logic-reducer-with-rewrite reducer rewrite)` | The reducer with the supplied callback representation. |

Every `(cons step reducer)` result may hold a failure in the step position.
`reduce`, `reduction`, `completion`, and `conditional` use `nil` there
when they make no change. The reducer is returned with its updated budget
and memo.

A rewrite callback is represented by `(t reply ...)`, with one
`(cons step lib)` per invocation, in invocation order. `step` can also
be `nil` or a failure. If a reply is needed, the step position is
`(:call :rewrite lib term)`. Evaluate the callback on the term and repeat
the original call with the new reply appended to the callback list in
the original reducer. The result reducer retains the unconsumed replies.

## Tree induction

The representation is `(:tree-induction lib formula variable measure
substitutions)`. Use the constructor and methods to work with it.
`extra` is an ordered list of two-element binding lists, empty by
default. These functions can return a failure in place of a step, including
the step position of `at`.

| ACL2 call | Result |
|---|---|
| `(book-logic-tree-induction-init lib formula variable)` | A tree induction measured by the count of `variable`. |
| `(book-logic-tree-induction-at induction value descent extra)` | `(cons step induction)`, with the displayed substitution appended. |
| `(book-logic-tree-induction-finish induction step)` | The proof using the stored substitutions. |

`match` can put a failure in `matched` when a malformed term is encountered.
`term-size`, `within-size` and `may-open` can return a failure for a malformed
term. `term-size` and `within-size` can also return a `Fuel` failure. Reducer
construction can return a failure when reading an evidence step.

The Reducer field accessors are `book-logic-reducer-evidence`,
`book-logic-reducer-definitions`, `book-logic-reducer-expose`,
`book-logic-reducer-budget`, `book-logic-reducer-size`,
`book-logic-reducer-rewrite`, `book-logic-reducer-logical` and
`book-logic-reducer-memo`. The TreeInduction field accessors are
`book-logic-tree-induction-lib`, `book-logic-tree-induction-formula`,
`book-logic-tree-induction-variable`, `book-logic-tree-induction-measure`
and `book-logic-tree-induction-substitutions`. Each accessor takes one
object and returns its indicated field.
