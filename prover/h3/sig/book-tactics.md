# Book tactics

A Library and a Step use the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. A term is a frozen prover term. `name` is the full
prover symbol, `kind` is the entry word as a string, and `fields` is the
ordered list of arguments to the statement. `aids` is the list of parsed
`(kind fields)` records in input order. An entry has the four fields
returned by `proof-proof-entry`.

## Search

A book search is the Search of `prover/h3/sig/rewrite.md` with its book
options installed. The constructor takes a Library, defined heads to
open, calls to open, Rules, a case budget, an inference budget, a
Boolean for deep rewriting, and a Boolean for opening arguments first.
The defaults after `lib` are `nil nil nil 14 130 nil nil`. The normalizing search uses the Search operations in that signature. Search state and
the list of recorded tests are returned even when the result is a failure.

| ACL2 call | Result |
|---|---|
| `(h3-book-tactics-book-search-init lib definitions calls rules budget inference-budget deep inside-first)` | A book search. |
| `(h3-book-tactics-book-search-reduce search term evidence tests active)` | `(list value search tests)` with an equality Step, `nil`, or a failure as `value`. |

## Fact index

A fact index is `(:h3-book-tactics-fact-index count formulas conclusions
equations)`. `count` is the number of facts seen by `extend`. Each table
is an insertion-ordered alist from a head to `(pattern name)` pairs in
fact insertion order. The head of an atomic term is `nil`. Use
`h3-book-tactics-fact-index-count`, `h3-book-tactics-fact-index-formulas`,
`h3-book-tactics-fact-index-conclusions`, and
`h3-book-tactics-fact-index-equations` to read the fields.

| ACL2 call | Result |
|---|---|
| `(h3-book-tactics-fact-index-init)` | An empty fact index. Does not produce a failure. |
| `(h3-book-tactics-fact-index-extend index lib)` | The updated fact index or a failure. |
| `(h3-book-tactics-fact-index-exact index lib formula)` | `(cons value index)`, with the first matching instantiated Step, `nil`, or a failure as `value`. |
| `(h3-book-tactics-fact-index-rules-for index lib terms)` | `(cons value index)`, with the names in rule selection order or a failure as `value`. |

## Theorem recipes

| ACL2 call | Result |
|---|---|
| `(h3-book-tactics-subterms term)` | List of subterms in preorder, retaining duplicates. |
| `(h3-book-tactics-decreasing-equation term)` | Whether the equation is directed toward a smaller term, or a failure. |
| `(h3-book-tactics-small-definitions lib terms)` | The ordered list of at most 35 small applications, or a failure. |
| `(h3-book-tactics-induction-candidates lib calls)` | A list of `(variable replacements)` pairs in source order, or a failure. Each replacement is `(mapping reason)` as in `prover/h3/sig/induction.md`. Substitution maps retain formal order. |
| `(h3-book-tactics-guarded-instance lib formula index)` | The guarded theorem Step, `nil`, or a failure. |
| `(h3-book-tactics-lookup-on-cons lib formula)` | The association-list lookup Step, `nil`, or a failure. |
| `(h3-book-tactics-structural-arithmetic lib formula)` | `(cons value lib)`, with a proof Step, `nil`, or a failure as `value`. |
| `(h3-book-tactics-pseudo-term-constructors lib)` | `(cons value lib)`, with the auxiliary fact's name or a failure as `value`. |
| `(h3-book-tactics-prove-clause-type lib formula)` | `(cons value lib)`, with a proof Step or failure as `value`. |

The constants are `*h3-book-tactics-iff*`, `*h3-book-tactics-definitions*`,
`*h3-book-tactics-boolean-rules*`, `*h3-book-tactics-fixed-rules*`,
`*h3-book-tactics-clause-types*`, `*h3-book-tactics-set-count-theorems*`,
`*h3-book-tactics-term*` and `*h3-book-tactics-terms*`. Rule and definition
lists retain their source order. The two sets of theorem names use
lexicographic order. An unqualified fact name can be passed to proof operations as a string.

## Induction and witness callbacks

An `evidence` argument contains Steps in the order supplied by induction.
`available` is the list of definition heads, and `calls` is the list of
applications that the search can unfold. `rules` is a Rules object from
`prover/h3/sig/rewrite.md`. `inside-first` has the meaning given for a book search.
All three callbacks return a Step or a failure.

| ACL2 call | Result |
|---|---|
| `(h3-book-tactics-solve-theorem-prove-case evidence lib available calls rules inside-first formula)` | The proof of `formula` for a structural induction case. |
| `(h3-book-tactics-prove-clause-type-prove-case evidence lib calls rules formula)` | The proof of the clause type formula for the case. |

`(h3-book-tactics-matching-theorem-with-index lib formula index)` pairs
the result of matching with the fact index reached by its exact lookups.
The result is `(cons value index)`, with a Step, `nil`, or a failure as
`value`.

`(h3-book-tactics-prepare-facts proof)` prepares the fact index of a
Proof. Its value also records each fact's insertion position and any
indexing failure at that position. A failure is reported by a tactic when
it needs the index.

The value is `(index positions errors names)`. `positions` is an association
list with the most recently inserted fact first. Each entry is
`(name position . contribution)`, where `position` starts at zero and
`contribution` contains the fact's index items or its failure. `errors`
pairs positions with failures. A tactic uses the failure at the earliest position. `(h3-book-tactics-prepared-fact-names prepared)`
returns `names`, the admitted fact names in reverse insertion order.

`(h3-book-tactics-update-prepared-facts prepared old-proof proof names)`
updates that value for the new Proof. `names` lists the added or updated
fact names in order of admission. Updating an existing fact keeps its
position. The caller supplies all names whose clause or definition
status may have changed.
