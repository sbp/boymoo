# Indexed call types and lengths

`lib` is a Library with the T3 proof rules. Terms, names and Steps use the
forms in `prover/sig/proof.md`. A theorem recipe takes its name symbol and
formula term and returns the entry `(kind name counts source)`. Each proof
operation can return a failure as its entire result.

| Call | Result |
|---|---|
| `(t3-book-indexed-calls-fix-value lib value type-proof)` | Equality Step for the exported natural fix of term `value`, using the signed natural type Step `type-proof`. |
| `(t3-book-indexed-calls-clip-nonpositive lib value nonpositive)` | Step equating the exported natural fix of `value` to zero, using the Step `nonpositive`. |
| `(t3-book-indexed-calls-indexed-type lib name formula)` | The theorem entry for type preservation over the interval. |
| `(t3-book-indexed-calls-indexed-length lib name formula)` | The theorem entry for the length over the interval. |
| `(t3-book-indexed-calls-full-length lib name formula)` | The theorem entry for the length from zero. |

The prover symbols are `*t3-book-indexed-calls-aux*`,
`*t3-book-indexed-calls-i*`, `*t3-book-indexed-calls-n*`, and
`*t3-book-indexed-calls-length-aux*`.

An Interval has the form
`(:t3-book-indexed-calls-interval lib call index end tests before next-index remaining measure pairs)`.
The constructor `(t3-book-indexed-calls-interval-init lib call)` computes
these fields from the Library and the call term. It can return a failure for a call
without two final arguments. The field accessors take an Interval and use
the prefix `t3-book-indexed-calls-interval-` followed by the field name.
The `tests` field lists the natural index test, the natural end test and
the strict interval comparison in that order. `pairs` is the singleton
list of the binding from the index to the next index.

`(t3-book-indexed-calls-interval-induction-case interval formula evidence)`
returns `(hypothesis numbers span-positive)`. `evidence` holds the three
positive Steps for the Interval's tests in order. `numbers` contains the
index and end integer Steps in that order.

`(t3-book-indexed-calls-interval-induct interval result formula)` returns
the induction Step from the case Step `result` and the formula term.

`(t3-book-indexed-calls-interval-cases interval prove)` gives the Step
obtained by joining the four interval cases. The `prove` argument is
`(:type normalized accepted)` for the type recipe's normalized formula
and accepted Step, or `(:length width span goal)` for the length recipe's
terms. A callback can also be supplied as `(:replies (key . reply) ...)`,
where `key` is `(bounds signed)` with the branch equation Step and its
ordered signed Steps, and a `reply` is a Step or a failure. The calls occur
for a non-growing interval, a growing interval, a nonnatural end, then a
nonnatural index. A missing reply returns `unproved`.

For the Library of a book proof context, use the `:t3-book` Proof dispatch tag
specified in `prover/t3/sig/logic.md`. It selects the book proof context natural
and integer proofs for exported `NFIX` terms.
