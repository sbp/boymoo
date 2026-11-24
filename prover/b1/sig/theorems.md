# Theorem recipes

`lib` is a B1 Library. A `formula` is a prover term, and a proof is a Step
as defined in `prover/sig/proof.md`.

`*b1-theorems-recipes*` is an ordered alist from label strings to recipe
symbols. Look up a label with `assoc-equal`. `*b1-theorems-unproved*`
lists labels of known unproved obligations. `*b1-theorems-list-recipes*`
is an ordered alist from operation strings to recipe symbols.
`*b1-theorems-bit-types*` lists bit type labels in source order.

| Call | Result | Failure |
|---|---|---|
| `(b1-theorems-apply-recipe label lib formula)` | `(cons step lib)` for the recipe selected by label string `label`, with the resulting Library and its entries in insertion order. | A failure for an unknown label or from the recipe. |
| `(b1-theorems-all-fnnames lib formula)` | Step proving the list type of the accumulator returned by `ALL-FNNAMES1`. | From the term shape or proof construction, including `Unproved` for an unchanged accumulator where an opening is required. |
| `(b1-theorems-realfix-rational lib term)` | Step proving the `REALFIX` application term `term` rational. | From the term shape or proof construction. |
| `(b1-theorems-complex-opener lib formula)` | Step proving the complex definition equality. | From the term shape or proof construction. |
| `(b1-theorems-predicate-equality lib formula booleans)` | Step equating equality and equivalence on the Boolean operands of `formula`. `booleans` is the list of their Boolean type Steps in operand order. | From the term shape or proof construction. |
| `(b1-theorems-equal-of-predicates lib formula)` | Step proving the predicate equality implication. | From the term shape or proof construction. |
| `(b1-theorems-linear-equalities lib formula)` | Step proving the equality and equivalence of comparisons agree. | From the term shape or proof construction. |
| `(b1-theorems-project-conjunct lib formula)` | Step proving an implication whose conclusion is a conjunct of its premise. | From the term shape or proof construction, including `Unproved` for an absent conjunct. |

`*b1-theorems-true-listp*`, `*b1-theorems-all-fnnames*`,
`*b1-theorems-add-to-set*`, `*b1-theorems-booleanp*`,
`*b1-theorems-iff*` and `*b1-theorems-realfix*` are symbol terms.

## FactIndex and recipe identity

`(b1-theorems-apply-recipe-with-index label lib formula index)` takes the
same arguments as `b1-theorems-apply-recipe` with the BookProof's FactIndex
as `index`. Pass `nil` for an absent index.

`(b1-theorems-apply-recipe-id recipe lib formula index)` takes a recipe
symbol from the cdr of a `*b1-theorems-recipes*` entry instead of a label.
It has the same success result and propagates a recipe failure. An unknown
symbol gives the generic failure.

A named recipe and a shape recipe use the same symbol when they select
the same function. Parameterized recipes carry distinct descriptors.
The certificate interface uses the recipe identifiers to try each recipe
once in dispatch order.
