# Power order

`lib` is a Library, and proof steps and terms have the forms in
`prover/sig/library.md` and `prover/sig/proof.md`. `context` is a Bounds object
from `prover/h3/sig/book-order.md`. Its evidence is used in insertion order. Proof lists are in argument order. `growing` and `strict`
are Booleans. Pass `nil` for the omitted `strict` argument of `unit-bound`.

A result of `(cons step lib)` includes the resulting Library, with any
auxiliary entries in the order they were added. In those results a missing
proof is `nil` in the first component. A failure can take the place of an
entire result.

| Call | Arguments and result | Failure |
|---|---|---|
| `(h3-book-power-order-unit-bound term growing strict)` | The strict or weak comparison of `term` with one. The lower endpoint is one when `growing` is true. | None. |
| `(h3-book-power-order-times-positive lib bound scalar positive types)` | Comparison Step, scalar rationality and positivity Steps, and a list of endpoint rationality Steps in operand order. Returns `(cons step lib)` for the scaled comparison. | A failure from proof construction. |
| `(h3-book-power-order-scaled-unit-bound lib bound scalar positive factor combined)` | A unit comparison Step, scalar rationality and positivity Steps, other endpoint rationality Step, and a Step rewriting the product of the nonunit endpoint and the scalar. Returns `(cons step lib)` for the simplified scaled comparison. | A failure from proof construction. |
| `(h3-book-power-order-advance-bound lib base positive base-bound exponent exponent-positive previous previous-bound growing)` | Steps for the base being rational, positive and ordered relative to one, the exponent being integer and positive, the predecessor being integer, and the predecessor's power bound. Returns `(cons step lib)` for the exponent's power bound. | A failure from proof construction or search. |
| `(h3-book-power-order-unit-lemma-name growing)` | The auxiliary lemma's name string for the given direction. | None. |
| `(h3-book-power-order-prove-unit-bound lib growing)` | The Library extended with the weak unit bound lemma in the given direction. | A failure from proof construction or search. |
| `(h3-book-power-order-unit-bound-natural lib base positive relative index nonnegative growing)` | Steps proving the base rational, positive and weakly ordered relative to one, and the index integer and nonnegative. Returns `(cons step lib)` for the weak bound of the power relative to one. | A failure from proof construction or search. |
| `(h3-book-power-order-unit-bound-positive lib base positive relative index index-positive growing)` | Steps proving the base rational, positive and strictly ordered relative to one, and the index integer and positive. Returns `(cons step lib)` for the strict bound of the power relative to one. | A failure from proof construction or search. |
| `(h3-book-power-order-compare-powers lib base positive relative first second exponent-bound growing)` | Steps for base rationality, positivity and order relative to one, the two exponents' integrality, and their ordering. Returns `(cons step lib)` for the corresponding power comparison. | A failure from proof construction or search. |
| `(h3-book-power-order-pair-base first second)` | The shared base term of two power terms, or the base of a power term paired with one. Returns `:none` when no shared base fits. | A failure when a required operand is absent. |
| `(h3-book-power-order-as-powers lib formula base)` | Comparison formula and base term. Returns an equality Step that rewrites unit endpoints as powers with exponent zero. | A failure from proof construction or search. |
| `(h3-book-power-order-compare-with-one lib formula context base positive low high strict)` | Comparison formula, Bounds, base rationality and positivity Steps, lower and upper endpoint terms, and strictness. Returns `(cons step lib)` for the direct comparison with one when its premises can be proved. | A failure from proof construction or a failed assertion. |
| `(h3-book-power-order-exponent-comparison n lib formula context)` | Natural-number fuel, Library, comparison formula and Bounds. Returns `(cons step lib)` for the comparison. Pass `1000000` as the initial fuel. | `Unproved`, `Fuel` or a failure from proof construction. |
| `(h3-book-power-order-equivalent-power-order lib goal context)` | Equality formula and Bounds. Returns `(cons step lib)` for the equality of the two comparisons when the goal matches. | A failure from proof construction or search. |
| `(h3-book-power-order-has-power-comparison formula)` | Whether the formula compares terms recognized by `pair-base`. | A failure from reading a malformed comparison or power call. |
| `(h3-book-power-order-integral-power-test lib goal context)` | Equality formula for testing the integrality of a power, and Bounds. Returns `(cons step lib)` for that equality. | A failure from proof construction or search. |
| `(h3-book-power-order-unit-power-in-window lib goal context)` | Equality of a power to one and Bounds for the interval from one to its base. Returns `(cons step lib)` for that equality. | A failure from proof construction or search. |
| `(h3-book-power-order-power-order-theorem lib formula)` | The formula term. Returns `(cons step lib)` for the recognized theorem. | A failure from proof construction or search. |

`(h3-book-power-order-power-order-theorem-with-library lib formula)`
returns a pair even when the value is a failure. A tactic dispatcher that
catches `Unproved` uses this entry point to retain the Library reached
by the search.

`(h3-book-power-order-unit-bound-natural-with-library lib base positive relative index nonnegative growing)`
uses the arguments of `unit-bound-natural`. It returns `(cons value lib)`
even when the value is a failure, retaining any lemmas added during the proof.
