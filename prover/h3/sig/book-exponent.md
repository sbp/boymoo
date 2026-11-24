# Exponent proofs

`lib` is a Library as specified in `prover/sig/library.md`. `context` is a
Bounds object from `book-order` whose evidence maps terms to Steps in
insertion order. Terms and Steps use the forms in `prover/sig/proof.md`.

Calls in the first table return `(cons value lib)`, where `lib` is the
Library after the call and `value` has the form given below. The value can
instead be a failure. The pair preserves any lemmas added before the failure.
An absent optional Step is `nil`.

| Call | Value |
|---|---|
| `(h3-book-exponent-type-and-bound lib term context)` | `(integer bound)`, the integrality Step and any available nonnegative bound for `term`. May return `Unproved` when the integer proof is missing, or a failure from a dependency. |
| `(h3-book-exponent-nonzero-base lib term context)` | `(numeric nonzero)`, Steps proving that `term` is numeric and nonzero. May return a failure from proof construction. |
| `(h3-book-exponent-exponent-theorem lib name formula)` | A Step for the given theorem, or `nil` when no recipe proves it. `name` is the theorem name string and `formula` is its term. May return a failure from inspecting the formula or constructing the proof. |
| `(h3-book-exponent-floor-power-shift lib statement exponent value)` | Step for the floor-shift equality `statement`, using the integer Step `exponent` and the floor argument term `value`. May return a failure from term access or proof construction. |
| `(h3-book-exponent-power-factor-value lib factor context)` | `(integer equality)`, the exponent type Step and the equality Step for `factor` expressed as a power. May return a failure from term access or proof construction. |
| `(h3-book-exponent-combine-power-factors lib first second target context)` | Step equating the product of the factor terms `first` and `second` to the power term `target`. May return a failure from term access or proof construction. |
| `(h3-book-exponent-power-product-equality lib goal context)` | Step for the product equality term `goal`, or `nil` when neither orientation gives a proof. May return a failure from term access or proof construction. |
| `(h3-book-exponent-power-shift-two-factors lib goal context)` | Step for the two-factor floor-shift equality term `goal`. May return `StopIteration` if a required factor is missing, or a failure from term access or proof construction. |
| `(h3-book-exponent-exponent-type-theorem lib goal term context)` | Step for the type or bound term `goal` about the power term `term`. May return a failure from term access or proof construction. |

The following calls return their value directly, or a failure in its place.

| Call | Result |
|---|---|
| `(h3-book-exponent-two-data lib)` | `(integer positive)`, the integrality and strict positivity Steps for the constant two. May return a failure from proof construction. |
| `(h3-book-exponent-product-factors term)` | The factors in left-to-right order, recursively flattening multiplication calls and retaining repeats. |
| `(h3-book-exponent-factor-as-power term)` | The power term inside a reciprocal or the power term itself, or `nil` if there is no such power. May return a failure on a malformed reciprocal. |
| `(h3-book-exponent-typed-power goal)` | The power term recognized inside an integer, rational, positive or nonnegative goal, or `nil` otherwise. May return a failure on malformed calls. |

`(h3-book-exponent-nonzero-base-with-context lib term context)` returns
`(cons value context)`, where `value` is the same as for `nonzero-base`
and the Bounds retains its current Library and Search. Use this call
when the same Bounds will be queried again.
