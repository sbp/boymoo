# Statement shapes

`lib` is the B1 library used by the proof recipes. A term has the form
specified in `prover/sig/proof.md`. In a term position, `:none` denotes an
absent term and `nil` denotes the empty list. In a recipe position,
`nil` denotes the absence of a recipe.

A plain recipe is the ACL2 symbol naming its function in the
`BOYMOO-PROVER` package. The two closures have the forms
`(:exponent-addition-goal sign)`, with sign `1` or `-1`, and
`(:natural-bit-length)`. For a theorem, invoke a plain recipe with
`lib` and the original formula, adding `0` as the third argument for
`b1-powers-exponent-addition-goal`. Invoke the two closures using the
lifted functions below. For a witness, invoke the named recipe with
`lib`, the list of function names and the original named formulas.
Each recipe retains its own result convention.

| Call | Arguments and result | Failure |
|---|---|---|
| `(b1-shapes-head term)` | Returns the head of a nonempty compound term, or `:none`. | None |
| `(b1-shapes-split-goal formula)` | Returns `(test goal)` for an implication, or `(:none formula)`. | Can return a failure on a malformed implication |
| `(b1-shapes-conjuncts test)` | Returns the conjuncts of the optional test in order. Each `IF` with quoted false as its third argument contributes its test before its true branch is visited. | Can return a failure on a malformed conditional |
| `(b1-shapes-revappend-recipe test goal subject)` | Returns the reverse-and-append recipe for the optional test, goal and subject. | Can return a failure on a malformed term |
| `(b1-shapes-association-recipe test subject)` | Returns the association list recipe for the optional test and subject. | Can return a failure on a malformed term |
| `(b1-shapes-set-recipe test goal subject)` | Returns the membership or set recipe for the optional test, goal and subject. | Can return a failure on a malformed term |
| `(b1-shapes-equality-of-fixes lib term)` | Returns whether the term's defining body tests two calls with the same head for equality. | Can return a failure on a malformed definition |
| `(b1-shapes-congruence-contrapositive lib formula)` | Returns the Step for the implication or `nil` when rewriting gives a different equality. | Can return a failure from reading a term or constructing a proof |
| `(b1-shapes-exponent-recipe test goal)` | Returns the exponent recipe for the optional test and goal. | Can return a failure on a malformed term |
| `(b1-shapes-arithmetic-recipe test goal subject)` | Returns the arithmetic recipe for the optional test, goal and subject. | Can return a failure on a malformed term |
| `(b1-shapes-witness-recipe functions formulas)` | Returns a witness recipe symbol or `nil`. `functions` is the ordered list of `(name arity)` pairs and `formulas` is the ordered list of `(name formula)` pairs. | Can return a failure on a malformed term or pair |
| `(b1-shapes-exponent-recipe-signed lib formula sign)` | Calls `b1-powers-exponent-addition-goal` with the formula and the captured sign. Returns `(cons step lib)` with the resulting Library. | A failure from the recipe |
| `(b1-shapes-theorem-recipes-natural-bit-length lib claim)` | Calls `b1-bit-length-natural-bit-length` on the argument of the claim. Returns the result of that recipe. | A failure from the recipe or a malformed claim |

`*b1-shapes-list-operations*` is an alist from operation symbols to
abstract list recipe symbols in insertion order. The operation lists
`*b1-shapes-set-operations*` and `*b1-shapes-member-operations*` retain
their source order. The constants `*b1-shapes-numerator*`,
`*b1-shapes-denominator*`, and `*b1-shapes-inverse*` are prover symbols.

## FactIndex

Pass the context's FactIndex separately. Use
`(b1-shapes-theorem-recipes-with-index lib formula index)` and
`(b1-shapes-abstract-list-recipe-with-index lib test goal subject index)`
for a BookProof with an available index. The corresponding calls above
use `nil` as their index. Pass the same index to each recipe that takes a
FactIndex.
