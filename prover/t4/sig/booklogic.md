# Book logic

Terms, symbols, Proofs and Steps have the forms given in
`prover/sig/proof.md`. A BookLogic has the form
`(:t4-booklogic library rules projected-rules equalities rule-heads
equality-heads premises enabled enhanced chaining project-returns
evaluate-syntax evaluators packages mutual recursive total-remaining
arithmetic remaining)`. Use the constructor and field operations below.
The Library contains the inherited Proof and the ordered list of auxiliary
entries. The evaluator rules use the form given in `evaluation.md`.

`rules` and `equalities` are dictionaries from rule keys to ordered lists
of `(name pattern)` pairs. `projected-rules` maps rule keys to ordered
lists of `(name path pattern)` triples. A rule key is
`(head discriminator)`, with `:none` for an absent discriminator.
`premises` maps heads to ordered lists of `(name premise)` pairs.
`mutual` maps each recursive function to the names in its mutual
recursion group, in definition order. Dictionary keys follow insertion
order. The lists for `rule-heads`, `equality-heads`, `enabled`,
`packages` and `recursive` keep distinct members in first-insertion
order. Their order does not determine proof search. The initial packages
are `("ACL2" "COMMON-LISP" "KEYWORD")`.

`(t4-booklogic-booklogic-init prefix)` takes a Proof and returns
BookLogic with the facts and definitions from that Proof added to the
ground Proof, then indexed in fact order. Initialization may return a
failure from reading or indexing the facts. The other operations on fields
do not return a failure.

The accessors `t4-booklogic-booklogic-library`,
`t4-booklogic-booklogic-evaluators`, `t4-booklogic-booklogic-packages`,
`t4-booklogic-booklogic-mutual`, `t4-booklogic-booklogic-recursive`,
`t4-booklogic-booklogic-enabled`, `t4-booklogic-booklogic-remaining`
and `t4-booklogic-booklogic-total-remaining` take BookLogic and
return the named field. The corresponding
`t4-booklogic-booklogic-with-library`,
`t4-booklogic-booklogic-with-evaluators`,
`t4-booklogic-booklogic-with-packages`,
`t4-booklogic-booklogic-with-mutual`,
`t4-booklogic-booklogic-with-recursive`,
`t4-booklogic-booklogic-with-enabled`,
`t4-booklogic-booklogic-with-remaining` and
`t4-booklogic-booklogic-with-total-remaining` take BookLogic and a
replacement field and return the resulting BookLogic. Use `:none` for
an absent budget. The accessors `t4-booklogic-booklogic-proof` and
`t4-booklogic-booklogic-entries` return the inherited Proof and entry
list. `(t4-booklogic-booklogic-with-proof book proof)` sets the
inherited Proof and returns BookLogic.

The constants `*t4-booklogic-zp*` and `*t4-booklogic-countdown*` are
the symbol `ZP` and the ordered list of countdown function symbols.
Pass `nil` for an omitted path in `conjuncts`. Except for `match`, the
functions below return the value directly. Each can return a failure from
reading a term, including a missing field of a term.

| Call | Result |
|---|---|
| `(t4-booklogic-term-size term)` | The number of term nodes, counting a quotation as one. |
| `(t4-booklogic-match pattern term bindings)` | `(cons matched-p bindings)` with the resulting insertion-ordered binding map, including bindings added by a failing match. |
| `(t4-booklogic-free-variables term)` | Variables in first-occurrence order, skipping heads and quotations. |
| `(t4-booklogic-calls-function term name)` | Whether the function occurs outside quotations and lambda heads. |
| `(t4-booklogic-constructor-result term)` | Whether the returned term is a cons, after following `RETURN-LAST` and lambda bodies. |
| `(t4-booklogic-has-constructor-result term)` | Whether a returned branch passes `constructor-result`. |
| `(t4-booklogic-rule-key term)` | The rule key for the term. |
| `(t4-booklogic-candidates rules term)` | Rules for the exact key, followed by rules for the head alone when the discriminator is present. |
| `(t4-booklogic-conjuncts formula path)` | The list of `(formula path)` pairs in left-to-right order. The path is a list of indices into the two proofs returned by `conjunct`. |

In the method calls below, `book` is BookLogic, `tests` is a list of
`(term holds)` pairs with Boolean `holds`, `extra` is a list of
additional Steps, and `evidence` is Evidence as in `structural.md`.
`depth` is the case depth, initially 0. `opened` is the list of heads
expanded along a path and `force-open` is Boolean. Use `nil` for an omitted list argument and `:none` for omitted induction
bindings.
Induction bindings are `(variable term)` pairs in insertion order.
Proof search can fail during term inspection or proof construction.
The solver and theorem entry points can report `"search-miss"` when
they find no proof. Queries for a Step can return `nil` when none applies.

| Call | Result on success |
|---|---|
| `(t4-booklogic-booklogic-index-fact book name clause)` | BookLogic with the eligible patterns of the named fact appended to their indexes. |
| `(t4-booklogic-booklogic-use-arithmetic book)` | BookLogic with the arithmetic library built if needed. |
| `(t4-booklogic-booklogic-branch-test book term)` | First term to split on, or `nil`. |
| `(t4-booklogic-booklogic-induction-variables book term)` | List of candidate variables in traversal order, including repeats. |
| `(t4-booklogic-booklogic-synchronized-selectors book formula)` | List of ordered substitution lists in recursive call and term order. |
| `(t4-booklogic-booklogic-consequences book evidence)` | `(list steps book evidence)`, with Steps in order of first discovery. |
| `(t4-booklogic-booklogic-constant book term)` | `(cons step book)` with an equality Step computing the constant when recognized. |

A method failure is the entire result. For calls that catch a proof search
failure and continue with the same BookLogic, the calls
`t4-booklogic-booklogic-solve-with-book` and
`t4-booklogic-booklogic-theorem-with-book` take the same arguments as
`solve` and `theorem` respectively and return `(cons result book)`
even when `result` is a failure.

`(t4-booklogic-nonempty-result-visit n value tests opened book limit)`
follows the reachable branches of `value` under the signed tests.
Pass `1000000` for the initial fuel `n`. The nonempty-result method
starts with a visit limit of 36. The result is `(list result book limit)`
with the proof or a failure and the remaining visit allowance.

`(t4-booklogic-booklogic-init-with-proof proof)` takes a base Proof
containing the ground facts, definitions and primitives, with any
in-scope replacements already applied. It initializes BookLogic and
indexes the facts in their existing order. A fact indexing failure is
the entire result.

The session form of BookLogic appends an index of sizes for admitted
definition bodies. Each entry is `(name body . size)`. The size is used
when the current definition has the stored body.

| Call | Result |
|---|---|
| `(t4-booklogic-lookup-tree entries)` | A balanced lookup tree of alist entries with distinct keys in ACL2's lexical order. May return `fuel`. |
| `(t4-booklogic-lookup-entry key tree)` | The alist entry for `key`, or `nil` when absent. |
| `(t4-booklogic-booklogic-cache-definition-sizes book)` | BookLogic with the sizes of its admitted definition bodies. May return a failure from building the tree. |
| `(t4-booklogic-booklogic-extend-definition-sizes book definitions)` | BookLogic with size entries from the supplied `(name formals body)` triples inserted or replaced. |
