# Book tactics

Terms, Steps and Libraries have the forms in `prover/sig/proof.md` and
`prover/sig/library.md`. The `library` argument is the H4 Tactics Library.
An evidence map is an insertion-ordered alist whose keys are the first
literals of its Steps. A binding map is an insertion-ordered alist of
`(variable . term)` entries. Proof methods receive the corresponding list of
`(variable term)` pairs when they instantiate a fact.

| Call | Result |
|---|---|
| `(h4-book-tactics-guarded-alias-proof library formula)` | Step for the guarded formula, `nil` if the search finds no match, or a failure. |
| `(h4-book-tactics-terms term)` | Argument subterms in preorder, including `term` and retaining duplicates. A quotation or an atomic term has no children. A lambda head is skipped. |
| `(h4-book-tactics-size term limit)` | Number of subterms counted, stopping at `limit`. Pass 150 for the usual bounded count. An integer limit outside the interval from 0 through 9223372036854775807 produces a failure. |
| `(h4-book-tactics-smaller first second)` | Whether `first` precedes `second` by size, with the written terms breaking ties for sizes below 150. Writing can return a failure. |
| `(h4-book-tactics-fits datum budget)` | Whether the datum fits the given integer budget, counting quoted data as well as terms. Malformed tagged data can return a failure. |
| `(h4-book-tactics-term-key term)` | `(head first-head)`, where `first-head` is `nil` for an absent or atomic first argument. Reading a malformed term can return a failure. |
| `(h4-book-tactics-views source formula path local clause)` | List of Rules in visit order. `source` is a fact name or a Step, `path` is a list of direction numbers and defaults to `nil`, and the two Boolean flags default to `nil`. Reading a malformed term can return a failure. |
| `(h4-book-tactics-equality-symmetry library)` | Library with the two local lemmas in declaration order, or a failure. |
| `(h4-book-tactics-canonical-comparisons library equality)` | Equality Step with canonical comparisons on the right side, or a failure. |

The constants are `*h4-book-tactics-iff*`, `*h4-book-tactics-booleanp*`,
`*h4-book-tactics-logic*`, `*h4-book-tactics-consp-cons*`,
`*h4-book-tactics-cons-equal-variables*`, `*h4-book-tactics-recursive*`, and
`*h4-book-tactics-equal-symmetry*`. The three constant lists use their order
of declaration. `*h4-book-tactics-consp-cons*` is a fact-name string.

## Rule

A Rule has the form `(:h4-book-tactics-rule source conclusion path local
clause)`. For a local Rule, `source` is a Step. For a global Rule, `source`
is a fact name. `conclusion` is the term matched by the Rule. `path` is the
ordered list of implication, conjunct and equivalence directions leading to
the conclusion. `local` and `clause` are Booleans. Use
`(h4-book-tactics-make-rule source conclusion path local clause)` to build
it, and use the `h4-book-tactics-rule-` accessors `source`, `conclusion`,
`path`, `local` and `clause` to read it.

## BookSearch

A BookSearch has the form `(:h4-book-tactics-book-search library
literal-rules equations remaining matches given extended-rules lookup-history
scope hypotheses-replies unrestricted-rewrite)`. Use the accessors and
updates below. Both rule indexes are insertion-ordered alists from term keys
to ordered lists of Rules. The indexes visit facts in reverse insertion
order and Rules for each fact in the order returned by `views`. `given` is
a list of Steps in argument order. `lookup-history` records resolved
lookups within an evidence scope so a repeated query keeps its effect on the
match budget. The remaining two fields supply hooks for a search that
extends these methods. The default hypothesis hook is `:default` and the
default unrestricted rewrite name is `nil`.

The accessors are `h4-book-tactics-book-search-p` for the Library,
and `h4-book-tactics-book-search-` followed by `literal-rules`, `equations`,
`remaining`, `matches`, `given` and `extended-rules` for the named fields.
`(h4-book-tactics-book-search-with-budgets search remaining matches)` and
`(h4-book-tactics-book-search-with-matches search matches)` return updated
BookSearch objects.

Calls returning `(cons result search)` carry the updated search even when
`result` is a failure. A `nil` Step means that there was no applicable rule.
Each method below can propagate a failure from a called proof operation.

| Call | Result |
|---|---|
| `(h4-book-tactics-book-search-init library)` | A BookSearch, or a failure. Its budgets start at 0, and extended rules are enabled. |
| `(h4-book-tactics-book-search-recursion search head)` | `(calls index)`, where Calls are in source order and `index` is the zero-based formal position or `nil` when no structural formal is selected. |
| `(h4-book-tactics-book-search-known-shape search term evidence)` | Whether the term is a constructor, a quotation or is known to be a cons or an atom. |
| `(h4-book-tactics-book-search-expandable search term evidence)` | Whether the defined call can be unfolded under the evidence. |
| `(h4-book-tactics-book-search-hypotheses search premises)` | Evidence map from the ordered premise Steps. |
| `(h4-book-tactics-book-search-instantiate search rule term evidence depth rewrite)` | `(cons result search)` with the Step, `nil` or a failure. `rewrite` defaults to `nil`. |
| `(h4-book-tactics-book-search-replay search rule bindings evidence depth)` | `(cons result search)` with the Step, `nil` or a failure. |
| `(h4-book-tactics-book-search-iff-direction search fact premise direction)` | Step for applying the IFF fact with the given premise in direction 3 or 4. |
| `(h4-book-tactics-book-search-candidates index term)` | Rules from the exact term key and then the key with a `nil` first head. With no first head the result of the second lookup is `nil`. |
| `(h4-book-tactics-book-search-lookup search goal evidence depth)` | `(cons result search)` with the first proof, `nil` or a failure. Depth defaults to 2. |
| `(h4-book-tactics-book-search-lookup-rule search goal evidence depth)` | `(cons result search)` with the first proof, `nil` or a failure, searching the rules for the goal. |
| `(h4-book-tactics-book-search-reduction search formula evidence)` | `(cons result search)` with an equality Step or a failure. |
| `(h4-book-tactics-book-search-solve search formula premises splits)` | `(cons result search)` with a Step or a failure. `premises` defaults to `nil` and `splits` to 3. |
| `(h4-book-tactics-book-search-induction-rule actual formal)` | `(test-head holds builtin-number)` for a supported change from the formal to the actual, or `nil`. |
| `(h4-book-tactics-book-search-induction-options search formula)` | List of induction plans in discovery order with repeats removed, or a failure. |
| `(h4-book-tactics-book-search-synchronized-countdown options)` | First countdown plan with the largest number of compatible substitutions, or `nil`. |
| `(h4-book-tactics-book-search-induction search formula argument branch holds cases splits)` | `(cons result search)` with a Step or a failure. `argument`, `branch`, `holds` and `cases` constitute the plan, and `splits` defaults to 3. |
| `(h4-book-tactics-book-search-prove search formula induction given)` | `(cons result search)` with a Step or a failure. `induction` defaults to `t` and `given` to `nil`. |

An induction plan is `(argument branch holds cases)`. Each case is
`(builtin-number bindings)`, with bindings in insertion order as a list of
`(variable term)` pairs. The Boolean `holds` identifies the recursive branch.

For an extending search, `(h4-book-tactics-book-search-with-hooks search
hypotheses-replies unrestricted-rewrite)` installs an alist from premise
lists to evidence maps and a fact name to replay before applying the ordinary
rewrite filters. Pass `:default` to use the base hypothesis method. A missing
hypothesis reply yields `(:h4-book-tactics-hypotheses-request premises)` in the
result position. Use `h4-book-tactics-hypotheses-request-p` and
`h4-book-tactics-hypotheses-request-premises` to read it. An extending search
can compute that evidence, add the reply, and repeat the call with its
original search budgets.

For callers that keep several evidence dictionaries, use
`(h4-book-tactics-book-search-begin-lookup-scope search)` to obtain
`(cons scope search)` with a fresh scope. Then use
`(h4-book-tactics-book-search-lookup-scoped search goal evidence depth scope)`
or
`(h4-book-tactics-book-search-replay-scoped search rule bindings evidence depth scope)`.
The scope stays the same while the evidence dictionary stays the same.
The scoped lookup and replay return the same result pairs as their
unscoped forms.

Pass `:none` for an unlimited `size` count. The Booleans `nil` and `t` act as limits 0 and 1.

A template table is an immutable map from fact names to clauses and their
keyed rule templates. An empty map is `nil`. The map uses `lexorder` and
compares exact keys with `equal`.

| Prepared call | Result |
|---|---|
| `(h4-book-tactics-tree-entry key tree)` | The `(key . value)` association or `nil`. |
| `(h4-book-tactics-tree-put key value tree)` | The map with the given key and value. |
| `(h4-book-tactics-remember-template name clause templates)` | A template table with the given name and clause prepared. A failure to construct templates is stored for use when the fact enters a search. |
| `(h4-book-tactics-prepare-templates facts definitions templates)` | A template table extended with the non-definition facts from the supplied alists. |
| `(h4-book-tactics-book-search-init-with-templates library tables)` | A BookSearch, or a failure. Uses a rule template when the current fact's name and clause match a table entry. The rules and their order are the same as in `h4-book-tactics-book-search-init`. |
