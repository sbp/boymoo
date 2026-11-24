# Arithmetic

An Arithmetic object uses the shared Library representation in
`prover/sig/library.md`. Its Proof carries the `:slice` keyword so inherited
proof rules select the arithmetic reflexive citation when present. Pass the
Library itself to the methods below. A term, Step, and signed test have the
forms in `prover/sig/proof.md` and `prover/sig/descent.md`. Omitted evidence,
integer premises, and definitions are empty lists. Library entries and all
maps retain insertion order.

The symbol constants are `*t2-arithmetic-nfix*`, `*t2-arithmetic-ifix*`,
`*t2-arithmetic-abs*` (the symbol for `INTEGER-ABS`),
`*t2-arithmetic-length*`, `*t2-arithmetic-atom*`,
`*t2-arithmetic-numerator*`, and `*t2-arithmetic-denominator*`.

Each call can return a failure unless stated otherwise. A failure replaces the
entire result.

| Call | Result |
|---|---|
| `(t2-arithmetic-arithmetic-build lib)` | The Arithmetic Library with its common deductions and the base Library build. |
| `(t2-arithmetic-arithmetic-reflexive lib term)` | The reflexive equality Step for the term. |
| `(t2-arithmetic-arithmetic-prove lib term evidence definitions)` | A Step proving the term using the given Step and definition-name lists. |
| `(t2-arithmetic-arithmetic-modus-ponens lib step evidence)` | The implication's consequent Step using the premise Step. |
| `(t2-arithmetic-arithmetic-conjunct lib step)` | The two Steps of the conjunction, test first. |
| `(t2-arithmetic-arithmetic-type-of lib term evidence)` | A Step proving the term integer. |
| `(t2-arithmetic-arithmetic-natural lib term)` | A Step proving the term natural. |
| `(t2-arithmetic-arithmetic-build-countdowns lib)` | The Library with the countdown lemmas. |
| `(t2-arithmetic-arithmetic-numeric-add-zero lib number)` | The Step for adding zero on the left of the term proved numeric by `number`. |
| `(t2-arithmetic-arithmetic-negate-successor lib)` | The Library with the negated successor lemma. |
| `(t2-arithmetic-arithmetic-unique-inverse lib value candidate zero candidate-number)` | The equality Step for the negation of `value` and `candidate`, using the zero-sum Step and the Step proving `candidate` numeric. |
| `(t2-arithmetic-arithmetic-known-nfix lib nfix natural)` | The equality Step eliminating the given `NFIX` call using the Step that its argument is natural. |
| `(t2-arithmetic-arithmetic-integral-count lib term premise)` | `(cons step lib)` for the count of the term proved integer by `premise`. |
| `(t2-arithmetic-arithmetic-build-weak-order lib)` | The Library with the weak-order lemmas. |
| `(t2-arithmetic-arithmetic-weak-shift lib bound offset integers)` | The weak comparison Step shifted by the offset term, using the integer Step list. |
| `(t2-arithmetic-arithmetic-compare-chain lib left right integers)` | The composition of the comparisons in the two Steps, using the integer Step list. |
| `(t2-arithmetic-arithmetic-as-weak lib strict integers)` | The weak comparison Step corresponding to the strict Step, using the integer Step list. |
| `(t2-arithmetic-arithmetic-ordinal-comparison lib a b integers)` | The equality Step relating ordinal and integer comparison of the two terms, using the integer Step list. |
| `(t2-arithmetic-count-comparison lib strict child-count parent-count integers)` | The `O<` Step for the counts, given the strict comparison of their integer values and the two Steps equating the counts to those values. |
| `(t2-arithmetic-reversed-successor lib before after)` | The equality Step rewriting the incremented index in the difference terms. |
| `(t2-arithmetic-gap-endpoints term)` | The list of `(lower upper inclusive-p)` triples yielded for the term, in generator order. |
| `(t2-arithmetic-positive-gap lib before hypotheses integers)` | `(list step lib hypotheses)` for positivity of the difference term using the strict endpoint test and the given integer Steps. |
| `(t2-arithmetic-positive-countdown lib before hypotheses integers)` | `(list step lib hypotheses)` for positivity of the measure term using the tests and the given integer Steps. |
| `(t2-arithmetic-clipped-predecessor lib integral positive-value)` | `(cons step lib)` for clipped predecessor descent from the integer and positivity Steps. |
| `(t2-arithmetic-clipped-decrease lib goal hypotheses)` | `(list step lib hypotheses)` for decrease of a clipped gap. |
| `(t2-arithmetic-rational-parts lib rational)` | The Steps for the integer numerator, integer denominator, and positive denominator, in that order, from the rationality Step. |
| `(t2-arithmetic-natural-from-sign lib integer-fact nonnegative)` | The naturalness Step from the integer and nonnegative Steps. |
| `(t2-arithmetic-natural-from-positive lib integer-fact pos)` | The naturalness Step from the integer and positive Steps. |
| `(t2-arithmetic-count-natural lib natural)` | `(cons step lib)` for the count of the term proved natural by the Step. |
| `(t2-arithmetic-negative-magnitude lib strict integers)` | The positivity Step for the magnitude of the negative integer, using the strict comparison Step and integer Step list. |
| `(t2-arithmetic-count-negative lib strict integers)` | `(cons step lib)` for the count of a negative integer, using the strict comparison Step and integer Step list. |
| `(t2-arithmetic-positive-absolute lib integral nonzero)` | `(cons step lib)` for positivity of the absolute value, using the integer and nonzero Steps. |
| `(t2-arithmetic-nonzero-numerator lib rational noninteger)` | `(cons step lib)` for the nonzero numerator, using the rationality and nonintegrality Steps. |
| `(t2-arithmetic-rational-count-decrease lib goal hypotheses)` | `(list step lib hypotheses)` for descent from the count of a noninteger rational. |

## Inherited arithmetic rules

These calls apply the Arithmetic type, naturalness, or implication rule
within the inherited methods. Each can return a failure. They return Steps.

| Call | Result |
|---|---|
| `(t2-arithmetic-rational lib term evidence)` | Rationality of a term from its integer evidence. |
| `(t2-arithmetic-number lib term evidence)` | The ACL2 number property of a term from its integer evidence. |
| `(t2-arithmetic-comparison lib a b integers)` | Equality of `a < b` and positivity of `b - a`. |
| `(t2-arithmetic-linear-equal lib left right integers)` | Equality of the terms from their common linear form. |
| `(t2-arithmetic-less-from-difference lib a b positive-difference integers)` | Strict comparison from a Step proving the difference positive. |
| `(t2-arithmetic-weak-from-difference lib a b nonnegative-difference integers)` | Weak comparison from a Step proving the difference nonnegative. |

## Queries on hypotheses

A decrease goal is the three-element term containing the ordinal comparison
symbol, child measure, and parent measure. The ordinary hypothesis
entry points take the underlying shared Hypotheses object. They use its
tests and cached evidence for lookups and the values of its `extra` map in
insertion order for premises.

For RulerFacts, `t2-arithmetic-positive-gap-query`,
`t2-arithmetic-positive-countdown-query`, `t2-arithmetic-clipped-decrease-query`,
and `t2-arithmetic-rational-count-decrease-query` take the same arguments
followed by a list of replies, initially empty. A completed call has the
same result and returns a failure as the ordinary entry point. A suspended call
returns a request recognized by `(t2-arithmetic-request-p value)`.
The accessors `t2-arithmetic-request-operation`,
`t2-arithmetic-request-term`, `t2-arithmetic-request-library`, and
`t2-arithmetic-request-hypotheses` each take a request and cannot fail.

The operation is `:find`, `:require`, or `:premises`. The term is the
queried term, or `nil` for `:premises`. Evaluate the request using the
library and hypothesis state supplied with it. Append a two-element
`(value hypotheses)` reply to the reply list and call the recipe again
with its original arguments. The value is the resulting Step or `nil` for
`:find`, the required Step for `:require`, or the ordered Step list for
`:premises`. The reply carries the resulting full hypothesis object.
Propagate a failure from the requested operation. Each call consumes replies
in order, so successive requests for the same term retain their effects.

`(t2-arithmetic-integer-premises steps)` returns the Steps whose first
literal calls `INTEGERP`, in input order. It can fail when reading a Step.

## Context and proof operations

The ordinary hypothesis entry points also take the RulerFacts context
described in `prover/t2/sig/guarded-selectors.md`. They perform the requested
context operations in order. The query entry points remain available for
callers that supply the operations themselves.

`(t2-arithmetic-simplify proof term evidence definitions)` returns the
simplification equality Step or `nil` when the term is unchanged.
`(t2-arithmetic-simplify-first proof step evidence definitions)` simplifies
the first literal of a Step. Both take the Proof component and use the
Arithmetic reflexive rule and the base constant rule. Either can fail.

`(t2-arithmetic-hypotheses-after-library hypotheses initial lib)` returns
the context with the new Library if its Library equals `initial`. It
preserves the context's other fields and cannot fail.

| Helper | Result |
|---|---|
| `(t2-arithmetic-has-lemma lib name)` | Truthy when the Library has the fact for the unprefixed lemma name string. |
| `(t2-arithmetic-first-at step index)` | The datum at zero-based index in the first literal of the Step. Can fail. |
| `(t2-arithmetic-hypothesis-query operation term lib hypotheses replies)` | The query value, resulting context, and remaining replies as a three-element list, or a request or failure. Pass `:plain` to query the context directly. |
| `(t2-arithmetic-with-queries ((name form) ...) result)` | Evaluates each binding in order and returns the first failure or request. Evaluates the result when every binding returns a value. |

A premises query requires RulerFacts or a reply supplying the premises.
A direct query with bare Hypotheses returns a failure.
