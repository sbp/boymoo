# Equivalence rewriting

Terms, names and Steps use the forms in `prover/sig/proof.md`. A BookSearch
and a Rule use the forms in `prover/h4/sig/book-tactics.md`. A place is a list
of positive argument indices, with the empty list denoting the root. A
binding map is an alist of `(variable . term)` entries in insertion order.

An Equivalence stores the BookSearch, relation symbol, evidence map, four
law Steps and lists of Rules and inverse triples. Its form is
`(:h4-equivalence search relation premises boolean reflexive symmetric transitive rules inverses)`.
Use the constructor in the table and the accessors
`h4-book-equivalence-equivalence-search`,
`h4-book-equivalence-equivalence-relation`,
`h4-book-equivalence-equivalence-premises`,
`h4-book-equivalence-equivalence-boolean`,
`h4-book-equivalence-equivalence-reflexive`,
`h4-book-equivalence-equivalence-symmetric`,
`h4-book-equivalence-equivalence-transitive`,
`h4-book-equivalence-equivalence-rules` and
`h4-book-equivalence-equivalence-inverses`. Each accessor takes the
Equivalence and returns its field without a failure.
`h4-book-equivalence-equivalence-with-search` takes the Equivalence and
its replacement BookSearch and returns the updated Equivalence without a
failure. The inherited proof operations use the BookSearch's library.

Evidence is an alist from literal to Step in the order returned by
`h4-book-measures-expand-evidence`. Rules are in the BookSearch literal-rule table's
key order, then in each key's rule order, with duplicates removed by
keeping the first occurrence. Inverse triples have the form
`(operator inverse identity)` and keep their first occurrence order.

Unless stated otherwise, proof results can be a failure from search, term
operations or proof construction. An open-ended recursive search can also
return `fuel`. Where an evaluation updates a search, a successful
ordinary result is `(cons result updated-object)`, where that object is the
Equivalence or the BookSearch passed in. A failure is the entire result.
In proof results, `nil` indicates an absent Step.

| Function | Arguments in order | Result |
|---|---|---|
| `h4-book-equivalence-positions` | Term, starting place (default `nil`) | List of `(subterm place)` pairs, root first, then arguments in source order, excluding descendants of quotes and function positions. |
| `h4-book-equivalence-inverse-operations` | Rule list | List of inverse triples, in rule order, trying the two sides of each rule and the two operand orders in source order. Duplicates are retained. May return a failure on a malformed Rule. |
| `h4-book-equivalence-equivalence-init` | BookSearch, relation symbol, library fact name, premise Step list | Equivalence whose laws come from the named fact. Returns `unproved` if its reflexivity law has a different relation. |
| `h4-book-equivalence-equivalence-reverse` | Equivalence, relation Step | Step for the relation with the operands exchanged. |
| `h4-book-equivalence-equivalence-compose` | Equivalence, two relation Steps | Step for the relation between the outside operands. |
| `h4-book-equivalence-equivalence-follow` | Equivalence, path map, left term, right term | Step that composes the path. A path map is an insertion-ordered alist from a term to `(predecessor equality-step)`. The initial term has a `nil` value. |
| `h4-book-equivalence-equivalence-true-value` | Equivalence, relation Step | Equality Step equating the relation with quoted T. |
| `h4-book-equivalence-setoid-proof` | BookSearch, formula term | Step or `nil`, paired with the updated BookSearch. `unproved` and `inapplicable-step` in the equivalence proof or final implication leave the goal open. |

The Equivalence constructor appends a lookup scope to the fields above.
`(h4-book-equivalence-equivalence-lookup-scope equivalence)` returns it
without a failure. The scope belongs to the premise dictionary. A congruence
lift starts a fresh BookSearch scope for the evidence dictionary it makes.

| Lifted function | Arguments in order | Result |
|---|---|---|
| `h4-book-equivalence-equivalence-equality-equal-when-true` | Hypothesis Step, Library, forward Equivalence, Step that proves the right relation | Equality Step for the positive case, or a failure. |
| `h4-book-equivalence-equivalence-equality-equal-when-false` | Hypothesis Step, Library, Step that proves the left relation, right relation term | Equality Step for the negative case, or a failure. |
