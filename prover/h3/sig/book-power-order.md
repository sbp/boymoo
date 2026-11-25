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
| `(h3-book-power-order-unit-lemma-name growing)` | The auxiliary lemma's name string for the given direction. | None. |
| `(h3-book-power-order-pair-base first second)` | The shared base term of two power terms, or the base of a power term paired with one. Returns `:none` when no shared base fits. | A failure when a required operand is absent. |
| `(h3-book-power-order-as-powers lib formula base)` | Comparison formula and base term. Returns an equality Step that rewrites unit endpoints as powers with exponent zero. | A failure from proof construction or search. |
| `(h3-book-power-order-has-power-comparison formula)` | Whether the formula compares terms recognized by `pair-base`. | A failure from reading a malformed comparison or power call. |

`(h3-book-power-order-power-order-theorem-with-library lib formula)`
returns a pair even when the value is a failure. A tactic dispatcher that
catches `unproved` uses this entry point to retain the Library reached
by the search.

`(h3-book-power-order-unit-bound-natural-with-library lib base positive relative index nonnegative growing)`
uses the arguments of `unit-bound-natural`. It returns `(cons value lib)`
even when the value is a failure, retaining any lemmas added during the proof.
