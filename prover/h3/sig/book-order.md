# Book order

A Bounds object has the form `(:h3-bounds library search evidence)`. `library`
is the Library in `prover/sig/library.md`. `search` is the Rewrite Search
configured to unfold `NOT`. `evidence` is an association list from proved
literals to Steps, in the insertion order of `Search.context` and the subsequent
wrapper expansion. The first proof recorded for a literal retains its place
and value. Use the constructor and accessors to work with Bounds.

The terms and Steps below have the forms in `prover/sig/proof.md`. A comparison
is either `(< low high)` or `(not (< high low))`. `strict` and `mirrored` are
Boolean arguments. Pass `nil` for the default `mirrored` and `0` for the default
`depth`. When both `library` and `bounds` are passed, `library` is the current
Library used by `bounds`.

| Call | Result |
|---|---|
| `(h3-book-order-bound-parts term)` | `(low high strict)` for a comparison, or `nil`. A malformed comparison can fail when a required operand is absent. |
| `(h3-book-order-bounds-init library evidence)` | Bounds formed from `evidence`, a list of Steps in premise order. May fail. |
| `(h3-book-order-bounds-lib bounds)` | The current Library. Does not produce a failure. |
| `(h3-book-order-bounds-search bounds)` | The current Search. Does not produce a failure. |
| `(h3-book-order-bounds-evidence bounds)` | The ordered map of literals to Steps. Does not produce a failure. |
| `(h3-book-order-bounds-with-library bounds library)` | Bounds using the given Library, with the same evidence and search budget. Does not produce a failure. |
| `(h3-book-order-bounds-rational bounds term)` | A Step proving `term` rational. May fail. |
| `(h3-book-order-bounds-numeric bounds term)` | A Step proving `term` an ACL2 number. May fail. |
| `(h3-book-order-bounds-compose bounds first second)` | `(cons step bounds)` for the composition of two comparison Steps. May fail. |
| `(h3-book-order-bounds-path bounds source destination strict mirrored)` | `(cons steps bounds)` with the first eligible path in breadth-first order. The Step list is in path order. May fail, including `Unproved` when no path exists. |
| `(h3-book-order-bounds-direct-bound bounds goal mirrored)` | `(cons step bounds)` for the proof of the comparison `goal`. May fail, including `Unproved`. |
| `(h3-book-order-bounds-reflect bounds first second)` | `(cons step bounds)` with an equality Step reflecting `first < second` through additive negation. `first` and `second` are terms. May fail. |
| `(h3-book-order-bounds-bound bounds goal)` | `(cons step bounds)` for the proof of the comparison `goal`, with reflection on a retry. May fail, including `Unproved`. |
| `(h3-book-order-constant-product library constant scalar scalar-type)` | An equality Step reducing `constant * scalar` for `0`, `1`, and `-1`, or proving reflexivity. `scalar-type` proves `scalar` rational. May fail. |
| `(h3-book-order-selected-sign library bounds rational)` | `(cons signs bounds)` for the first provable sign, testing positive before negative. `rational` is a rationality Step and `signs` is the value from `book-signs`, or `nil` if neither sign is proved. May fail. |
| `(h3-book-order-quotient-bound library goal bounds depth)` | `(cons step bounds)` proving the comparison `goal` by clearing reciprocals. May fail, including `Unproved`. |
| `(h3-book-order-scaled-bound library goal bounds)` | `(cons step bounds)` proving the comparison `goal` by the sign of a common factor. May fail, including `Unproved`. |
| `(h3-book-order-product-bound library goal bounds)` | `(cons step bounds)` proving the comparison `goal` using comparisons through an intermediate product. May fail, including `Unproved`. |
| `(h3-book-order-product-zero-bound library goal bounds)` | `(cons step bounds)` proving the comparison `goal` by the sign of a factor. May fail, including `Unproved`. |
| `(h3-book-order-bound-tactic goal)` | `:quotient-bound`, `:product-bound`, `:product-zero-bound`, or `nil`, denoting the selected tactic. Malformed terms can fail. |
| `(h3-book-order-bound-atoms term)` | List of conjuncts, recursively visiting the test then the true branch of each `IF` with false other branch. A malformed `IF` can fail when a required operand is absent. |
| `(h3-book-order-nonlinear-theorem library formula)` | `(cons step library)` with the proof and any auxiliary lemmas, or `nil` when the tactic is inapplicable. May fail, including `Unproved`. |

In the paired results, the returned Bounds contains the current Library and
Search. A failure is the entire result. The comparison graph uses premise
order, placing a reflected edge after its original edge, then adds constant
comparisons in the order in which their terms were first recorded. A search
mark is a term together with a Boolean indicating whether its path was strict.

`*h3-book-order-hypothesis-wrappers*` lists the `CASE-SPLIT` and `FORCE` symbols
in that order.

The entries for `bounds-compose`, `bounds-path`, `bounds-direct-bound`,
`bounds-reflect`, `bounds-bound`, `selected-sign`, `quotient-bound`,
`scaled-bound`, `product-bound` and `product-zero-bound` each have a variant
with `-with-bounds` appended to the ACL2 name. The arguments are the same.
Each variant returns `(cons result bounds)` even when `result` is a failure.
Use these variants when a later proof attempt needs the resulting Bounds.
`h3-book-order-constant-product-with-library` and
`h3-book-order-nonlinear-theorem-with-library` likewise retain the Library in
`(cons result library)`. The negative unit case of `constant-product` can add
the lemma for moving a negation outside a product.
