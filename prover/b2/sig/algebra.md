# Algebra

`lib` is a Library as described in `prover/sig/library.md`. Terms, symbols, and Steps have the forms described in `prover/sig/proof.md`. A proof result can be a failure in place of the result in the table. A function that can add a lemma returns `(cons step lib)` with the resulting Library, including when the lemma was already present.

| Call | Result |
|---|---|
| `(b2-algebra-boolean-equivalence-positive lib goal yes forward)` | Step for the positive branch of `goal`, the equality of the tests, using the assumption Step `yes` and the forward recipe result. |
| `(b2-algebra-boolean-equivalence-negative lib left right no positive backward)` | Final Step using the false assumption Step `no`, the completed `positive` branch, and the backward recipe result. Use these two branch functions in sequence when a callback has effects or evaluation order matters. |
| `(b2-algebra-congruence lib equality term path)` | Step obtained by rewriting `term` with the equality Step at the argument indices in `path`. Pass `nil` for an empty path. |
| `(b2-algebra-fix-number lib value)` | Pair of the Step that proves `(ACL2-NUMBERP (FIX value))` and the Library. |
| `(b2-algebra-fixed-operand lib term position)` | Step inserting `FIX` at operand `position` of the sum or product `term`. The positions are 1 and 2. |
| `(b2-algebra-minus-fix lib value)` | Step inserting `FIX` under the negation of `value`. |
| `(b2-algebra-cancel-sum lib value offset)` | Step cancelling the addition and subtraction of `offset` around `value`. |
| `(b2-algebra-fixed-order lib a b)` | Step inserting `FIX` at both operands of the comparison of `a` and `b`. |
| `(b2-algebra-cancel-shift-difference lib offset a b)` | Step cancelling `offset` from the difference of its sums with `a` and `b`. |
| `(b2-algebra-cancel-common-shift lib offset a b)` | Step cancelling `offset` from the comparison of its sums with `a` and `b`. |
| `(b2-algebra-minus-equality lib left right)` | Step equating the test `left`, an equality of negations, to the test `right` on the completed operands. |
| `(b2-algebra-operand-cancellation lib left right)` | Pair of the Step for cancellation of the common right operand in `left`, with result `right`, and the Library. |
| `(b2-algebra-common-operand lib formula)` | Pair of the Step for the cancellation equality `formula` and the Library. The common operand can be on either side. |
| `(b2-algebra-product-zero-test lib a b)` | Pair of the Step equating the zero test on the product of `a` and `b` to zero tests on their completed factors, and the Library. |
| `(b2-algebra-cancel-inverse lib left right)` | Step equating the zero test `left` on a sum with its cancellation test `right`. |
| `(b2-algebra-arithmetic-identity lib name formula)` | Pair of the Step for the arithmetic theorem named by the symbol `name` and the Library. Returns `unproved` for an unsupported theorem. |

`*b2-algebra-names*` maps the addition and multiplication symbols to `"+"` and `"*"` in that insertion order. `*b2-algebra-cancellation*` and `*b2-algebra-arithmetic-theorems*` are sets of theorem symbols, ordered by their serialized forms.
