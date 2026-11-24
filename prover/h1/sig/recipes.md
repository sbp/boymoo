# Opening and induction plans

The argument `p` is the H1 Prover described in `prover/h1/sig/tactics.md`, including any subclass fields preserved by its accessors. A formula is a prover term, and a Step has the form in `prover/sig/proof.md`. Pass every listed argument. In `definition-equation`, pass `nil` for the default openings. Openings are a list of function symbols or an insertion-ordered dictionary of function symbols to depths. In `changed-calls`, pass `(list 1)` for the default place. A missing result from a probe is `nil`.

The three entry points used outside the book are `definition-equation`, `prove-by-shape` and `prove`. A result specified as a pair is `(cons step updated-p)`, where the step may be `nil` for a probe with no match. Any failure is the entire result. The dictionary of a Prover's facts is scanned in insertion order. Template binding pairs are passed to instantiation in the order in which matching bound the variables.

| ACL2 call | Result | Failure |
|---|---|---|
| `(h1-recipes-definition-equation p formula functions)` | Step proving the equation by unfolding its left side and, if needed, solving the residual equation with the given openings. | From destructuring, unfolding or solving. |
| `(h1-recipes-prove-by-shape p formula)` | Pair with the Step selected by the formula's shape. | `Unproved` if no plan applies, or a failure from the selected plan. |
| `(h1-recipes-prove p name formula)` | Pair with the Step selected by the unqualified theorem name string, falling back to automatic proof. | From the selected plan. |
| `(h1-recipes-function name p)` | The ACL2 symbol for the name string if defined, otherwise its Common Lisp symbol. | — |
| `(h1-recipes-openings p names)` | List of the symbols for the whitespace-separated names in the given string, in that order. | — |
| `(h1-recipes-conclusion formula)` | The consequent after peeling the formula's leading implications. | From reading a malformed implication. |
| `(h1-recipes-add-swap p)` | Step for the commutation of the first two addends in a right-associated sum. | From proof construction. |
| `(h1-recipes-distribute-minus p)` | Step for distribution of unary minus over addition. | From proof construction. |
| `(h1-recipes-changed-calls original target place)` | Ordered list of `(place original-call target-call)` triples for call-head substitutions, using one-based argument indices appended to `place`. | `Unproved` for different arguments. |
| `(h1-recipes-transfer-step p formula step)` | Pair with the Step obtained by proving call equations and rewriting at the changed places. | `Unproved` for different arguments, or a failure from proof construction. |
| `(h1-recipes-transfer-property p formula earlier)` | As for `transfer-step`, starting with the fact named by `earlier`. | From fact lookup or transfer. |
| `(h1-recipes-basic-types p formula)` | Pair with the Step using the basic type rules and auxiliary lemmas. | From proof construction. |
| `(h1-recipes-complex-equality p formula)` | Step for equality of complex numbers in terms of their parts. | From destructuring or proof construction. |
| `(h1-recipes-nonempty-package p formula)` | Step that a symbol has a nonempty package name. | From destructuring or proof construction. |
| `(h1-recipes-package-imports p formula)` | Pair with the Step for the default package imports. | From proof construction. |
| `(h1-recipes-reverse-property p formula character-lists)` | Pair with the Step for the reverse-append property selected by the Boolean `character-lists`. | From proof construction. |
| `(h1-recipes-true-list-helper p)` | Prover with the auxiliary true-list facts. | From proof construction. |
| `(h1-recipes-last-cdr p formula)` | Pair with the Step for the last cdr of a true list. | From proof construction. |
| `(h1-recipes-pairlis-tail p formula)` | Pair with the Step for the tail-recursive pair-list property. | From proof construction. |
| `(h1-recipes-ordinals p formula)` | Pair with the Step obtained by opening ordinal definitions and selectors. | From proof construction. |
| `(h1-recipes-position-type p formula)` | Pair with the Step that the position call returns a natural number or nil. | From reading the formula or proof construction. |
| `(h1-recipes-substitute-type p formula)` | Pair with the Step for the true-list result of substitution. | From proof construction. |
| `(h1-recipes-remove-duplicates-type p formula)` | Pair with the Step for the character-list result of removing duplicates. | From proof construction. |
| `(h1-recipes-recognizer-spine p formula)` | Step for a recognized property of the list spine on a cons, or `nil`. | From reading the formula or proof construction. |
| `(h1-recipes-both terms)` | The right-associated conditional conjunction of the ordered terms. | A failure for zero terms. |
| `(h1-recipes-solve-templates p formula)` | Pair with the instantiated Step for the first matching template, or with `nil` when none matches. | From matching or solving the selected template. |
| `(h1-recipes-position-call formula)` | The application recognized in a natural-or-nil property, or `nil`. | From reading a malformed formula. |
| `(h1-recipes-natural-result p formula application)` | Pair with the Step transferred from the first applicable fact or obtained by induction. | From reading facts, matching or proof construction. |
| `(h1-recipes-calls-operator term operator)` | Whether the term calls the given operator outside quotations, including calls inside lambda bodies. | From reading a malformed lambda. |

The call-substitution traversal and arithmetic method requests use natural-number fuel. These operations can also return a `Fuel` failure if they exhaust it.

The branch proof functions take the listed arguments in order. Each returns a Step or a proof construction failure.

| ACL2 call | Result |
|---|---|
| `(h1-recipes-distribute-minus-assoc x y z p)` | The associativity axiom instantiated at the three terms. |
| `(h1-recipes-distribute-minus-commute x y p)` | The commutativity axiom instantiated at the two terms. |
| `(h1-recipes-distribute-minus-zero-plus term numeric p)` | The equality of zero plus `term` to `term`, given the numberhood Step `numeric`. |
| `(h1-recipes-complex-equality-component part p c1 whole r1 i1 r2 i2)` | The equality of the selected parts of the two complex terms. `part` is `"REALPART"` or `"IMAGPART"`, `c1` is the first complex term, and `whole` proves equality to the second. The four remaining Steps prove the parts rational in real and imaginary order for each term. |
