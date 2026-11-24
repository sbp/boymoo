# Concatenating list maps

`p` is a Library as specified in `prover/sig/library.md`. Terms and Steps
have the forms in `prover/sig/proof.md`. These calls leave the Library
unchanged. A failed proof operation returns the failure as its entire result.

| ACL2 call | Arguments and result | Failure |
|---|---|---|
| `(h4-book-flatten-unfold-on-list p call sequence shape)` | Equality Step for the expansion of `call` at the given `sequence`. Pass `nil` when no shape Step is supplied. | Yes. |
| `(h4-book-flatten-rewrite-argument p call index equality)` | Reflexivity of `call` rewritten on the right at the one-based argument `index` by the equality Step. | Yes. |
| `(h4-book-flatten-cdr-induction-recurse shape p formula sequence changes)` | Induction-hypothesis Step under the supplied positive `CONSP` assumption Step `shape`. `changes` is the ordered list of additional `(variable term)` bindings, or `nil`. | Yes. |
| `(h4-book-flatten-cdr-induction p formula sequence base step changes)` | Induction Step for `formula`. `base` is the atom-case Step and `step` is the cons-case Step. | Yes. |
| `(h4-book-flatten-append-associativity p)` | Associativity Step for binary append. | Yes. |
| `(h4-book-flatten-revappend-after-append p)` | Step distributing `REVAPPEND` over append. | Yes. |
| `(h4-book-flatten-concat-map p mapper first second)` | Step distributing a unary `mapper` over append of terms `first` and `second`. | Yes. |
| `(h4-book-flatten-map-accumulator p mapper executable sequence accumulator)` | Step relating the accumulator implementation and the unary list map. `mapper` and `executable` are function names. | Yes. |
| `(h4-book-flatten-map-after-list-fix p mapper)` | Step showing that a unary `mapper` is invariant under list fixing. | Yes. |
| `(h4-book-flatten-append-map-shape formula)` | Matching shape `("concatenation" mapper first second)`, `("accumulator" mapper executable sequence accumulator)`, `("equivalence" mapper first second)`, or `nil`. | A malformed application can return a failure. |
| `(h4-book-flatten-append-map-proof p formula)` | Step for a supported list-map formula, or `nil`. | An `InapplicableStep` leaves the goal open. Other failures can propagate. |

To supply induction cases, build the positive assumption using
`proof-proof-assume` on `(CONSP sequence)`. Use it with
`h4-book-flatten-cdr-induction-recurse` to obtain the hypothesis and
construct `step`. Then build the negative assumption and `base`.
Pass both Steps and the same `changes` to `h4-book-flatten-cdr-induction`.

The constants are `*h4-book-flatten-append*`, `*h4-book-flatten-list-fix*`,
`*h4-book-flatten-list-equiv*`, `*h4-book-flatten-revappend*`, and
`*h4-book-flatten-logic*`. The last is the list of logic symbols in
source order.

## Proof operations

These operations take a Library and can return a failure. They implement
the proof operations used by the list and measure recipes.

| ACL2 call | Result |
|---|---|
| `(h4-book-flatten-normalize p term evidence expand rewrites)` | Equality Step from the term to its normal form. Evidence and explicit rewrite Steps are in insertion order. `expand` is a list of definition names. |
| `(h4-book-flatten-establish p formula evidence expand rewrites)` | Step proving the formula using the same ordered arguments as normalization. |
| `(h4-book-flatten-case-of p formula test yes no)` | Step joining the positive and negative case Steps, each with first literal `formula`. |
| `(h4-book-flatten-imply p formula conclusion)` | Step restoring the implication `formula` from its conclusion Step. |
| `(h4-book-flatten-conjunction p formula first second)` | Step introducing the conjunction of the two Steps in `formula`. |
| `(h4-book-flatten-conjunct p step)` | Pair of Steps in a two-element list, first for the test and then for the true branch of the conjunction. |
| `(h4-book-flatten-modus-ponens p step evidence)` | Step for the consequent of the implication Step using its premise Step. |
| `(h4-book-flatten-nil-value p negative)` | Equality to quoted NIL, from a Step establishing negation. |
| `(h4-book-flatten-non-nil p equality)` | Step proving the left-hand term from an equality to a non-NIL quoted value. |
| `(h4-book-flatten-fact-instance p term evidence names rewrite)` | First applicable fact Step, or `nil`. Pass `:none` to search facts in insertion order, or a list of names to search in list order. `rewrite` selects matching on the equation's left-hand term. |
| `(h4-book-flatten-step-right step)` | The right term in the first equality literal of `step`. An absent literal or term can return a failure. |
| `(h4-book-flatten-binding-map bindings result)` | The alist `result` updated with the two-element binding lists in `bindings`. The first occurrence of each key fixes its position, and the last supplies its value.  |
