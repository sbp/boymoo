# Constructed ordinals and measure comparisons

An Ordinals object uses the Library representation and constructor in
`prover/sig/library.md`. Terms and Steps have the forms in
`prover/sig/proof.md`. Evidence has the form specified by
`prover/t4/sig/structural.md`. Each call can return a failure from a failed
proof operation or term operation. A failure is the entire result.

In a `(cons step lib)` result, the Library includes any lemmas added in
the call, in insertion order. Use `nil` for absent Steps. Optional evidence and definition sequences use `nil` when
omitted. An evidence sequence is a list of Steps unless it is identified
as an Evidence object.

| Call | Arguments and result |
|---|---|
| `(t4-ordinals-ordinals-simplify lib term evidence definitions)` | Simplify the term under the evidence and list of definition symbols to unfold. Return `(cons step lib)` with the equality Step or `nil` as the Step when unchanged. |
| `(t4-ordinals-ordinals-constant lib term)` | Constant computation equality for a term, returned as `(cons step lib)` with `nil` as the Step when inapplicable. |
| `(t4-ordinals-ordinals-true-boolean lib boolean truth)` | `(cons step lib)` for the equality of a term to quoted T, given a Boolean Step and a truth Step about the term. |
| `(t4-ordinals-ordinals-type-of lib term evidence)` | Integer Step for the term. |
| `(t4-ordinals-ordinals-natural lib term)` | Natural Step for the term. |
| `(t4-ordinals-ordinals-imply lib antecedent consequent)` | Step introducing an implication, from an antecedent term and consequent Step. |
| `(t4-ordinals-ordinals-distinct lib strict integers)` | Step denying equality of the endpoints of strict comparison Step `strict`, given the integer Steps `integers`. |
| `(t4-ordinals-ordinals-constructor-view lib operator term)` | `(cons step lib)` for an equality opening selector symbol `operator` on a constructed ordinal term. |
| `(t4-ordinals-ordinals-view-ordinals lib goal constructors)` | `(cons step lib)` for the unfolded goal term with each constructor term's selectors rewritten in order. returns a failure if a constructor is not a MAKE-ORD call. |
| `(t4-ordinals-ordinals-make-ordinal lib term exp-nat exp-positive coeff-positive rest-ordinal exp-order coeff-int)` | `(cons step lib)` for ordinality of the MAKE-ORD term. The following arguments are Steps establishing exponent naturalness and positivity, coefficient positivity, ordinality of the rest, exponent ordering, and optional coefficient integrality. |
| `(t4-ordinals-ordinals-order-blocks lib left right smaller exp-equal coeff-equal)` | `(cons step lib)` for order between two MAKE-ORD terms. `smaller` proves the first differing component is smaller. The optional equality Steps concern the exponents and coefficients. |
| `(t4-ordinals-ordinals-finite-below-block lib finite block)` | `(cons step lib)` for order between integer term `finite` and MAKE-ORD term `block`. |
| `(t4-ordinals-ordinals-weak-distinct lib weak distinct evidence)` | `(cons step lib)` strengthening weak comparison Step `weak`, given a disequality Step and an integer evidence Step list. |
| `(t4-ordinals-ordinals-phase-ordinal lib term)` | `(cons step lib)` for ordinality of the exponent-one MAKE-ORD term. returns a failure for another exponent. |
| `(t4-ordinals-ordinals-phase-measure-ordinal lib measure)` | `(cons step lib)` for ordinality of the measure term, lifting the phase proof through conditionals and lambdas. |
| `(t4-ordinals-ordinals-phase-decrease lib left right bound)` | `(cons step lib)` for the phase order between two phase measure terms, given an optional size bound Step. Can return a failure `Fuel` on exhaustion. |
| `(t4-ordinals-ordinals-decide-test lib test evidence)` | `(cons step (cons lib evidence))` for a decision about the test term, with `nil` as the Step if undecided, using and returning an Evidence object. |
| `(t4-ordinals-ordinals-compare-measures lib goal tests replies)` | `(cons step lib)` for the comparison goal term, using a signed test list and the leaf replies described below. Can return a failure `Fuel` on exhaustion. |
| `(t4-ordinals-phase-measure size phase)` | The exponent-one measure term for the size and phase terms. No failure. |

The comparison recipe requests leaf calls in traversal order. A request
has the form `(:t4-ordinals-request left right evidence lib)`.
`t4-ordinals-request-p` recognizes it, and `t4-ordinals-request-left`,
`t4-ordinals-request-right`, `t4-ordinals-request-evidence`, and
`t4-ordinals-request-library` return its fields. Start with `nil` replies,
append the requested leaf's `(cons step lib)` or failure, and repeat the call
with its original Library, goal and tests.

The term constants are `*t4-ordinals-make*`, `*t4-ordinals-finite*`,
`*t4-ordinals-exponent*`, `*t4-ordinals-coefficient*`,
`*t4-ordinals-rest*`, `*t4-ordinals-posp*`, `*t4-ordinals-booleanp*`,
`*t4-ordinals-numeric-eq*`, `*t4-ordinals-u*`, `*t4-ordinals-v*`, and
`*t4-ordinals-w*`.

`(t4-ordinals-ordinals-prove lib term evidence definitions)` applies the
inherited proof recipe with Ordinals simplification. It returns
`(cons step lib)` or a failure. The same result convention applies to
`(t4-ordinals-ordinals-simplify-first lib step evidence definitions)`,
which simplifies the first literal of a Step, and
`(t4-ordinals-ordinals-natural-with-library lib term)`, which retains
any lemmas added while proving that the term is natural.

`(t4-ordinals-nonnil-selection lib reduced)` returns an equality Step
and selected branch term as a two-element list when the test of the
conditional term `reduced` is a non-nil quotation. It returns `nil`
when this reduction does not apply, or a failure from the proof operations.

`(t4-ordinals-prove-premise lib term evidence)` returns a Step for the
term when it is quoted T or is the first literal of an evidence Step.
Search is in evidence order. It returns `nil` when there is no such
Step, or a failure from the proof operations.
