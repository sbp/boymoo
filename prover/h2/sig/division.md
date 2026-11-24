# Integer product order and division

`lib` is the Library from `prover/sig/library.md`, and terms and Steps have the
forms in `prover/sig/proof.md`. `search` is the H2 Search with its current
Library and rule configuration. Evidence is an ordered list of Steps.
The term constants `*h2-division-numerator*`, `*h2-division-denominator*`,
`*h2-division-floor*`, `*h2-division-rationalp*`, `*h2-division-quotient*`,
`*h2-division-posp*`, `*h2-division-zp*`, `*h2-division-print-base*`,
`*h2-division-explode*` and `*h2-division-reciprocal*` are the corresponding
prover symbols. `quotient`, `print-base`, `explode` and `reciprocal` stand
for `NONNEGATIVE-INTEGER-QUOTIENT`, `PRINT-BASE-P`,
`EXPLODE-NONNEGATIVE-INTEGER` and `UNARY-/`.

| ACL2 call | Result |
|---|---|
| `(h2-division-product left right)` | The binary product of the two terms. Does not failure. |
| `(h2-division-identity-factor lib term evidence)` | A Step evaluating the product of one and `term`, or a failure. |
| `(h2-division-positive-product lib left right positive-left positive-right integers)` | A Step proving the terms' product positive, or a failure. The two positivity arguments are Steps and `integers` is the ordered integer evidence. |
| `(h2-division-product-order lib)` | The Library with the zero product, positive product order and cancellation lemmas, or a failure. |
| `(h2-division-subtraction-descent lib)` | `(cons name lib)` with the subtraction descent lemma and its name string. |
| `(h2-division-count-of-natural lib)` | `(cons name lib)` with the count of a natural lemma and its name string. |
| `(h2-division-quotient-bounds search)` | `(cons name search)` with the quotient bounds lemma and its name string. |
| `(h2-division-multiply-ratio search ratio divisor numerator integers pos-divisor)` | `(cons step search)` with a Step multiplying the ratio equality by its divisor. `ratio` and `pos-divisor` are Steps and `divisor` and `numerator` are terms. |
| `(h2-division-floor-bounds search)` | `(cons name search)` with the floor bounds lemma and its name string. |
| `(h2-division-print-base-bounds search)` | `(cons name search)` with the print base bounds lemma and its name string. |
| `(h2-division-make-recognizer definitions facts repeat)` | A recognizer for the accumulator induction, using the definition names, ordered fact names, and repeat definition names of `h2-division-derive`. |
| `(h2-division-explode-true-list search formula)` | `(cons step search)` with a proof of the true-list accumulator invariant `formula`. |
| `(h2-division-explode-accumulator search formula recognize)` | `(cons result search)` for the accumulator invariant `formula`, with a Step or a recognition request as `result`. |

Pairs carry the Library or Search as it stands on return. A pair can
carry a failure in its first field. Use `:true-list` for the true-list
recognizer, or make a recognizer with the rule configuration for the
accumulator invariant. The induction calls the configured search at
each recognition site with the invariant Step as evidence.
`h2-division-recognizer-p` recognizes this record.
`h2-division-recognizer-definitions`, `h2-division-recognizer-facts`,
and `h2-division-recognizer-repeat` read its fields.

The accumulator also accepts explicit recognition replies in invocation
order. Each reply is `(cons step search)`, with a Step or a failure in
its first field. When a reply is needed, the result is
`(:call :recognize search claim evidence)`. Evaluate the recognition
function on `claim` and the single evidence Step in the supplied Search,
then repeat the original call with its reply appended. The Library's
facts and entries retain insertion order.

A Search operation can also return a request from an inherited method as
specified in `prover/h2/sig/search.md`. The request occupies the value position
and the caller supplies the inherited-method reply before repeating the call.

| Shared call | Result |
|---|---|
| `(h2-division-derive search formula definitions facts variable depth repeat seeds cases split-limit)` | `(cons step search)` for `formula`, or a failure or request in the Step position. The definition and repeat arguments are space-separated definition name strings. `variable` is a name string or `nil`. `depth` and `split-limit` are integers. `facts`, `seeds`, and `cases` are ordered lists of fact names, Steps, and terms. |
| `(h2-division-step-at step index)` | The field at the zero-based natural-number index in the Step's first literal, or a failure. |
| `(h2-division-with-search search bindings body)` | A macro for sequential bindings that propagates a failure or request paired with the current Search. A binding is `(name form)`, `(name form :search)` for a value and Search pair, or `(name form :library)` for a new Library. |
