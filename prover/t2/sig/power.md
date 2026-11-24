# Integer exponent laws

`lib` is the Library described in `prover/sig/library.md`. Terms and Steps
have the forms in `prover/sig/proof.md`. The constants `*t2-power-zip*`,
`*t2-power-ifix*`, and `*t2-power-equal-num*` are the symbols `ACL2::ZIP`,
`ACL2::IFIX`, and `COMMON-LISP::=`.

## Term and Step operations

`base` and `exponent` are terms. A Step argument named for a premise
proves that premise in its first literal. Lists of premises and conditions
retain the supplied order. A substitution `pairs` is a list of `(variable
term)` lists in insertion order. A boolean uses `t` for true and `nil`
for false.

| Function | Arguments in order | Result |
|---|---|---|
| `t2-power-power` | `base`, `exponent` | The `EXPT` term |
| `t2-power-condition` | List of premise terms | Their right-associated conjunction, with the last premise as the final branch |
| `t2-power-join` | `lib`, list of premise Steps | Step for the conjunction in premise order |
| `t2-power-conjuncts` | `lib`, conjunction Step, integer `count` | List of `count` Steps separated from the right-associated conjunction. For `count` at most one, the result is the singleton list of the given Step |
| `t2-power-implication` | `lib`, antecedent term, conclusion Step | Step for the implication from the antecedent to the conclusion |
| `t2-power-smaller-instance` | `lib`, induction formula term, Step for the measure decrease, substitution `pairs`, list of premise Steps | Step for the consequent at the smaller measure |
| `t2-power-zip-equation` | `lib`, `exponent`, Step proving integer exponent | Step equating `ZIP` of the exponent to equality of the exponent and zero |
| `t2-power-zero-power` | `lib`, `base`, Step equating the exponent to zero | Step equating the power to one |
| `t2-power-nonzero-zip` | `lib`, `exponent`, Step proving integer exponent, Step proving the exponent different from zero | Step denying `ZIP` of the exponent |
| `t2-power-split-power` | `lib`, `base`, `exponent`, Step proving integer exponent, Step proving nonzero exponent, Step affirming or denying that the fixed base is zero | Step opening `EXPT` and selecting the case of the fixed base |
| `t2-power-fixed-nonzero` | `lib`, Step proving the base numeric, Step proving nonzero base | Step proving nonzero fixed base |
| `t2-power-nonintegral-exponent` | `lib`, `base`, Step denying integer exponent | Step equating the power to one |
| `t2-power-nonzero-power` | `lib`, `base`, `exponent`, Step proving numeric base, Step proving nonzero base | Step proving nonzero power |
| `t2-power-exponent-number-leaf` | Leaf term, list of signed tests, `lib` | Step proving the leaf numeric |
| `t2-power-exponent-cases` | `lib`, Step proving integer exponent | `(cons ((predecessor positive-decrease) (successor negative-decrease)) lib)` with the Library after the countdown deductions |
| `t2-power-recurrence-from-smaller` | `lib`, `base`, Step proving integer exponent, Step proving the smaller exponent integer, Step proving numeric base, Step proving nonzero base, boolean `forward` | Step expressing the power in terms of the smaller exponent, using the successor law when `forward` holds and the predecessor law otherwise |
| `t2-power-numeric-from-fixed-nonzero` | `lib`, `base`, Step proving the fixed base nonzero | List of the Step proving numeric base and the Step proving nonzero base, in that order |
| `t2-power-summands-of-natural-zero` | `lib`, Step equating the sum to zero, list of two nonnegativity Steps, list of two integer Steps | `(cons (left-zero right-zero) lib)` with the Library after the deduction of positivity from nonzero |
| `t2-power-rational-power` | `lib`, Step proving the base rational, `exponent` | Step proving the power rational |
| `t2-power-base-conditions` | Boolean `increasing` | List of base condition terms. The increasing case gives `1 < X`. The decreasing case gives `0 < X` followed by `X < 1` |
| `t2-power-adjacent-change` | `lib`, boolean `increasing` | `(cons (step conditions) lib)` with the comparison Step, the list of its premise Steps, and the resulting Library |
| `t2-power-distance-decrease` | `lib`, lower term, upper term, Step proving lower less than upper, list of integer Steps | Step proving descent in their integer distance |
| `t2-power-shift-integer-order` | `lib`, first comparison term, second comparison term, list of integer Steps | Step equating the two comparisons |
| `t2-power-equal-predecessor` | `lib`, lower term, upper term, predecessor term, Step proving lower less than upper, list of integer Steps | Step equating the lower term and the predecessor of the upper term under the adjacency condition |

The term constructors `t2-power-power` and `t2-power-base-conditions`
cannot fail. The other operations can return a failure in place of the
entire result. An empty premise sequence in `condition` or `join` gives
a failure.

## Library operations

Each of these functions takes `lib` and returns the Library with the entries
added by the recipe, or a failure. Functions with an `increasing` argument
take it after `lib`.

| Function | Added entries |
|---|---|
| `t2-power-exponent-number` | Numeric type of `EXPT` |
| `t2-power-recurrence-lemmas` | Successor and predecessor laws |
| `t2-power-integer-exponent-test` | `ZIP` and integer completion |
| `t2-power-boundary-values` | Zero and one exponents, noninteger exponent, and zero and fixed-zero base |
| `t2-power-zero-power-comparison` | Nonzero power with reversed equality and the test for zero power |
| `t2-power-addition-in-the-field` | Addition at a nonzero base, including the reversed zero test |
| `t2-power-addition-with-zero-bases` | Addition including zero bases |
| `t2-power-addition-with-one-sign` | Addition for nonnegative and nonpositive exponents |
| `t2-power-positive-powers` | Positivity of an integer power of a positive rational |
| `t2-power-power-signs` | Positivity and nonnegativity with exponent completion |
| `t2-power-unit-base` | Unit base |
| `t2-power-monotonicity` (`increasing`) | Strict exponent order and its adjacent case |
| `t2-power-weak-exponent-order` (`increasing`) | Weak exponent order with strict and inclusive base conditions |
| `t2-power-comparisons-with-one` (`increasing`) | Comparisons with one for positive and negative exponents |
| `t2-power-exponent-comparisons` | Equivalence of exponent and power comparisons |
| `t2-power-adjacent-exponents` | Order bounds using the successor of the lower exponent and predecessor of the upper exponent |
| `t2-power-integral-powers` | Integrality of powers of integers |
| `t2-power-build` | All of the exponent entries in recipe order |

The proof recipes use the Arithmetic Library methods described in
`prover/t2/sig/arithmetic.md`. The exponent cases pass their integer and
negative evidence to the countdown through a RulerFacts context.
