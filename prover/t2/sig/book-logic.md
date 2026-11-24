# Book formulas

Terms, clauses, and Steps have the forms in `prover/sig/proof.md`. `lib` is a
Library as in `prover/sig/library.md`. A signed test is `(term holds)`, with
`t` for true and `nil` for false. A sequence of signed tests is in path
order. `(:failure "Unproved" "")` is the failure for a formula beyond
the search. Other returns a failure use `prover/CONVENTIONS.md`.

The symbol constants are `*t2-book-logic-car*`, `*t2-book-logic-cdr*`,
`*t2-book-logic-expt*`, `*t2-book-logic-iff*`, `*t2-book-logic-fix*`,
`*t2-book-logic-rfix*`, `*t2-book-logic-divide*`, `*t2-book-logic-zip*`,
`*t2-book-logic-zp*`, `*t2-book-logic-nfix*`, `*t2-book-logic-ifix*`, and
`*t2-book-logic-synp*`. `*t2-book-logic-completion*` and
`*t2-book-logic-boolean-axioms*` are alists in declaration order.
`*t2-book-logic-unfold*` is a set of symbol datums in serialized order.

| Call | Result | Failure |
|---|---|---|
| `(t2-book-logic-head term)` | The first element of a nonempty compound term, or `nil`. | None. |
| `(t2-book-logic-wrapper-equation lib term)` | The unfolding Step for a call to an argument-forwarding wrapper, or `nil`. | May fail during unfolding. |
| `(t2-book-logic-size term)` | The number of term nodes, counting a quotation as a single node. | None. |
| `(t2-book-logic-variables term)` | The distinct variables, ordered by their printed sort keys. | None on terms. |
| `(t2-book-logic-match pattern actual bindings)` | `(cons matched bindings)` with the Boolean match result and the insertion-ordered binding alist, including any bindings made before a failed match. | May fail on malformed terms. |
| `(t2-book-logic-arithmetic-constant datum)` | The ACL2 rational for an integer or a tagged ratio, or `nil`. | May fail on a malformed datum or a zero denominator. |
| `(t2-book-logic-fraction-datum value)` | The integer or tagged ratio for the ACL2 rational `value`. | None on rational input. |
| `(t2-book-logic-split-cons datum)` | The pair of selector values, as a two-element list. | May fail on a malformed dot tag. |
| `(t2-book-logic-cons-datum first rest)` | The datum for the cons of the two unquoted datums. | None. |
| `(t2-book-logic-constant lib term)` | The computation Step for a recognized constant call, or `nil`. | May fail in argument inspection or proof construction. |
| `(t2-book-logic-flattened operator term)` | Operands of the binary `operator`, in left-to-right order. | May fail on a malformed binary call. |
| `(t2-book-logic-simpler a b)` | Whether term `a` precedes `b` by size, with quotations first at equal size. | None. |
| `(t2-book-logic-true-boolean lib boolean positive)` | `(cons step lib)` with the equality-to-true Step and the Library including the auxiliary lemma. `boolean` proves the Boolean type and `positive` proves the term. | May return a failure. |
| `(t2-book-logic-ac-equal lib first second)` | An equality Step for `first` and `second`, or `nil`. | May fail in term writing or proof construction. |

## Rule index

A Rule is `(name pattern path reverse)`, where `name` is a fact name,
`pattern` is a term, `path` is a list of the strings `"consequent"`,
`"first"` and `"second"`, and `reverse` is a Boolean. Use
`t2-book-logic-rule-name`, `t2-book-logic-rule-pattern`,
`t2-book-logic-rule-path`, and `t2-book-logic-rule-reverse` to read a Rule.

A Rules object is `(:t2-rules lib goals equations indexed)`. `goals`
and `equations` are alists keyed by term head, with keys in insertion
order and rules in each bucket in insertion order. `indexed` records
names in the order in which they were first encountered. The accessors
are `t2-book-logic-rules-lib`, `t2-book-logic-rules-goals`,
`t2-book-logic-rules-equations`, and `t2-book-logic-rules-indexed`.

| Call | Result |
|---|---|
| `(t2-book-logic-rules-init lib)` | The Rules object indexed from `lib`, or a failure. |
| `(t2-book-logic-rules-update rules lib)` | Rules extended with facts from the current Library `lib` in the Library's fact order, or a failure. |
| `(t2-book-logic-rules-add rules name formula path)` | Rules including the entries for the given fact, formula and path, or a failure. Use `nil` for the root path. |

## Search

A Search is `(:t2-search lib rules hints budget contexts active failed
premises seeds hooks replies)`. `rules` is a Rules object, or `nil` for
normalization without rules. `hints` is the list of definition names in
first-occurrence order, `budget` is the remaining integer search budget,
and `seeds` is the ordered list of seed Steps. `contexts` maps signed
test lists to `RulerFacts` in insertion order. `active` and `failed`
record goal keys in insertion order, and `premises` is an insertion-ordered
alist keyed by `(goal tests depth)`. `hooks` and `replies` are empty for
the base search. The accessors are `t2-book-logic-search-lib`,
`t2-book-logic-search-rules`, `t2-book-logic-search-hints`,
`t2-book-logic-search-budget`, `t2-book-logic-search-contexts`,
`t2-book-logic-search-active`, `t2-book-logic-search-failed`,
`t2-book-logic-search-premises` and `t2-book-logic-search-seeds`.

| Call | Result |
|---|---|
| `(t2-book-logic-search-init lib rules hints budget seeds)` | A Search. Use `nil`, `3600`, and `nil` for the default hints, budget and seeds. |
| `(t2-book-logic-search-proof search goal tests depth)` | `(cons step search)` with a proof of `goal` and the resulting Search. Use `nil` and `5` for the default tests and depth. |
| `(t2-book-logic-search-try-prove search goal tests depth)` | The same pair, with `nil` as its value when no proof is found. |
| `(t2-book-logic-search-context search tests)` | `(cons context search)` with the `RulerFacts` for `tests` and the resulting Search. |
| `(t2-book-logic-search-normalize search term context depth opened)` | `(cons step (cons search context))` with the equality Step or `nil`, and the resulting Search and `RulerFacts`. `opened` is the list of terms or heads already opened on the path. Use `nil` for its default. |
| `(t2-book-logic-search-replacement search term context depth opened)` | The same form, for one replacement. |
| `(t2-book-logic-search-can-open search term opened)` | Whether to unfold `term`, or a failure. |

The Search calls returning pairs put a failure in the value position and
return the Search with its current Library. Read that Library with
`t2-book-logic-search-lib` before retrying a failed search.

For a derived normalizer, `(t2-book-logic-search-with-hooks search hooks
replies)` configures the overridden methods. `hooks` is a list drawn from
`:normalize`, `:replacement`, and `:can-open`. `replies` is a list in
invocation order. When a reply is required the value position is a request
recognized by `t2-book-logic-search-request-p`. The request accessors are
`t2-book-logic-search-request-method`, `t2-book-logic-search-request-term`,
`t2-book-logic-search-request-context`, `t2-book-logic-search-request-depth`,
`t2-book-logic-search-request-opened`, and
`t2-book-logic-search-request-lib`. Repeat the original call with the reply
appended to the original Search's replies. A reply of `:base` selects the
base implementation. A normalize reply `(:chain step target opened)`
chains `step` with the result of recursively normalizing `target` on the
given path. A replacement or can-open reply can be the corresponding
method's value, including `nil` or a failure. A reply of the form
`(:with-state value lib context)` also supplies an updated Library and
`RulerFacts`.

`(t2-book-logic-search-first-test search term)` returns the first test in
the term, `nil` if there is no test, or a failure on a malformed conditional.
Pass `nil` for the unused `search` argument.

## Prepared rules

`(t2-book-logic-rules-prepare lib)` returns the prepared rule clauses and
index for `lib`. A rule indexing failure is recorded in the prepared value.
`(t2-book-logic-rules-from-prepared prepared lib)` returns the same Rules
object or failure as `t2-book-logic-rules-init` on the supplied Library. It
reuses the prepared index for an extension and keeps the fact order of
the supplied Library.

`(t2-book-logic-prefix-suffix prefix lines)` returns `(cons t suffix)`
when `prefix` is a prefix of `lines`, or `nil` otherwise. It does not
failure.
