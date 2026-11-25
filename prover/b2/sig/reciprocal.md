# Reciprocal arithmetic

A Library and a Step have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. Every function may return a failure as its entire
result. A pair is `(cons value lib)` with the Library after the call.
Evidence is an ordered list of Steps.

The theorem names are `*b2-reciprocal-minus-zero*`,
`*b2-reciprocal-invert-twice*`, `*b2-reciprocal-invert-product*`,
`*b2-reciprocal-invert-minus*`, `*b2-reciprocal-cancel-right*`,
`*b2-reciprocal-cancel-left*`, `*b2-reciprocal-zero-product*`,
`*b2-reciprocal-product-x*`, `*b2-reciprocal-product-y*`,
`*b2-reciprocal-inverse-equal*`, `*b2-reciprocal-numerator-nonzero*`,
`*b2-reciprocal-injective*`, `*b2-reciprocal-ratio-unit*`,
`*b2-reciprocal-move-left*` and `*b2-reciprocal-move-right*`.
`*b2-reciprocal-reciprocal-theorems*` lists those names for membership tests.

| Call | Result |
|---|---|
| `(b2-reciprocal-reciprocal-theorem lib name formula)` | Pair with the Step proving theorem `name` with the given formula. |
| `(b2-reciprocal-equal-swap lib a b)` | Step proving that the equality tests on terms `a` and `b` agree in both operand orders. |
| `(b2-reciprocal-invert-unit lib unit typed)` | Pair with a reciprocal equality Step. `unit` proves a product equals one, and `typed` proves its first factor numeric. |
| `(b2-reciprocal-invert-involutively lib goal)` | Pair with the Step for the double reciprocal equation. |
| `(b2-reciprocal-invert-factors lib goal)` | Pair with the Step distributing the reciprocal over a product. |
| `(b2-reciprocal-invert-negation lib goal)` | Pair with the Step for the reciprocal of a negation. |
| `(b2-reciprocal-remove-reciprocals lib formula right)` | Step for the cancellation formula. Boolean `right` selects right cancellation. |
| `(b2-reciprocal-boolean-zero-product lib goal)` | Pair with the Step reducing the zero test on a product. |
| `(b2-reciprocal-product-same lib goal compare-second)` | Pair with the Step characterizing equality of a product to its first or second factor. Boolean `compare-second` selects the second. |
| `(b2-reciprocal-inverse-equality lib formula)` | Step proving the equivalence between an inverse and a product equation. |
| `(b2-reciprocal-rational-numerator lib term premise)` | Step proving `term` rational from the numerator premise Step. |
| `(b2-reciprocal-numerator-forward lib formula)` | Step proving the numeric and nonzero conclusion. |
| `(b2-reciprocal-reciprocal-injective lib goal)` | Pair with the Step for the equality of two reciprocals. |
| `(b2-reciprocal-reciprocal-numerator lib formula)` | Pair with the Step for the reciprocal when the numerator is one or minus one. |
| `(b2-reciprocal-move-divisor lib formula reverse)` | Step moving the reciprocal factor across the equality. Boolean `reverse` places that factor on the right of the product. |

`prove` in `numeric-nonzero-cases` is the list of callback replies in
invocation order. Each reply is `(cons step lib)`. For a missing reply
the value in the result pair is `(:call :numeric-nonzero lib active evidence)`.
Call the callback with `lib`, the Boolean `active`, and `evidence`, and
repeat the original call with the reply appended. `active` is true for a
numeric nonzero value. A failure may be supplied in place of a reply.

`(b2-reciprocal-evidence-at known term)` returns the Step for `term` in
the evidence table `known`, or a failure if it is absent.

The following macros abbreviate calls in proof recipes. `lib` is the
Library variable. A `branch`, `forward`, or `backward` expression produces
a pair with its Step and Library, or a failure.

| Macro | Expansion behavior |
|---|---|
| `(b2-reciprocal-results lib bindings result)` | Evaluate bindings in sequence and propagate a failure immediately. A binding `(name form :library)` binds `name` to the value and `lib` to the Library from a pair. An ordinary `(name form)` binds the whole result. |
| `(b2-reciprocal-return lib form)` | Pair the result of `form` with `lib`, propagating a failure. |
| `(b2-reciprocal-choose lib test evidence sign facts branch)` | Run the branch for each required case of `test`. `sign` is its Boolean sign and `facts` the ordered case evidence. Returns a pair with the joined Step. |
| `(b2-reciprocal-imply lib antecedent consequent premise branch)` | Bind `premise` to the Step assuming `antecedent` and run `branch` to prove `consequent`. Returns a pair with the implication Step. |
| `(b2-reciprocal-equivalence lib left right assumption forward backward)` | Run the Boolean equivalence recipe with `assumption` bound to the corresponding assumption Step for each direction. Returns a pair with the equality Step. |
| `(b2-reciprocal-normalize lib term evidence unfold rules)` | Normalization with the default budget and without branching. The last three arguments can be omitted. |
| `(b2-reciprocal-solve lib term evidence unfold rules branches)` | Proof search with zero unresolved splits. The last four arguments can be omitted. |
| `(b2-reciprocal-rewrite lib step equation place)` | Proof rewrite with default place `(1)`. |
| `(b2-reciprocal-tidy lib step)` | Proof tidying for the Step. |
| `(b2-reciprocal-symmetric lib step)` | Proof symmetry for the Step. |
| `(b2-reciprocal-chain lib first ... )` | Chain of its equality Steps in argument order. |
| `(b2-reciprocal-assume lib term holds)` | Proof assumption, with the default sign `t`. |
| `(b2-reciprocal-axiom lib name ... )` | Library axiom with its terms in argument order. |
