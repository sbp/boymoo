# Reversed accumulators

The `p` argument is a Tactics Library as specified in `prover/h4/sig/tactics.md`. Terms and Steps have the forms in `prover/sig/proof.md`. A match is `(executable logical accumulator)`, with both call terms and the accumulator term in that order. Tests are a list of evidence Steps in branch order. The symbol `*h4-book-accumulator-count-cells*` names the count formula used for pairs.

| Call | Result |
|---|---|
| `(h4-book-accumulator-reverse-accumulator-shape formula)` | The match for `formula`, or `nil`. |
| `(h4-book-accumulator-opened-call p term tests)` | The equality Step for unfolding and normalizing `term` under `tests`. |
| `(h4-book-accumulator-count-cells p cells shape)` | The count equality Step for `cells` with the evidence Step `shape`. |
| `(h4-book-accumulator-mapped-count p term equation)` | The mapped count equality Step using the `equation` Step. |
| `(h4-book-accumulator-count-pair-bound p left right left-head left-tail strict)` | The bound Step obtained by combining the head and tail bounds. `left`, `right`, `left-head`, and `left-tail` are Steps, and `strict` is Boolean. |
| `(h4-book-accumulator-map-selector-count p mapper selector)` | The weak count bound Step for the mapping function symbol `mapper` and the selector symbol `selector`. |
| `(h4-book-accumulator-mapped-descent p subject child tests parent)` | The strict ordinal descent Step using the evidence Step `parent` for the pair `subject`. |
| `(h4-book-accumulator-accumulator-induction p formula match subject)` | The Step for `formula` using its `match` and the induction variable `subject`. |
| `(h4-book-accumulator-reverse-accumulator-proof p formula)` | The first accumulator proof Step for `formula`, in logical argument order, or `nil`. |

Every call may return a failure as its entire result. A nonapplicable mapping or induction case may return a failure `unproved`. The last call handles `unproved` from its attempts and propagates other failures.
