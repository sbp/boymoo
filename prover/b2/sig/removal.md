# Removal clause processors

Terms, Steps, and the Library have the forms in `prover/sig/proof.md` and
`prover/sig/library.md`. A pair is `(cons value library)` with the resulting
Library. A failure is the entire result. Evidence is a list of Steps in the
order supplied.

| Call | Result | Failure |
|---|---|---|
| `(b2-removal-evaluated term state)` | The evaluator call on `term` and evaluation environment `state`. Pass the symbol `A` for the standard environment. | — |
| `(b2-removal-truth term)` | The conditional that maps `term` to quoted `T` or quoted `NIL`. | — |
| `(b2-removal-quote-evaluates library term state)` | The Step evaluating the quoted term in the given environment. | Failure from proof construction. |
| `(b2-removal-tests library conditions prove evidence)` | A pair with the case proof and the resulting Library, or a request described below. `conditions` is the list of test terms and `evidence` is the list of Steps already in scope. | Failure from proof construction or a callback reply. |
| `(b2-removal-disjoin-pair library)` | A pair with the disjunction lemma name and the Library containing it. | Failure from proof construction. |
| `(b2-removal-disjoin-truth library lst state)` | A pair with the Step for the truth of the disjunction of list term `lst` in environment `state`. | Failure from proof construction. |
| `(b2-removal-conjoin-single library lst)` | A pair with the Step equating the conjunction of a single clause `lst` and its disjunction. | Failure from proof construction. |
| `(b2-removal-first-hypothesis library formula)` | A pair with the Step proving the first-hypothesis processor correctness formula. | Failure from reading the term or constructing the proof. |
| `(b2-removal-denied-terms library premise source state cons)` | A pair with the two Steps denying the evaluated head and tail disjunction, given the refusal Step `premise`, list term `source`, evaluation environment `state` and cons Step `cons`. | Failure from proof construction. |
| `(b2-removal-remove-false library source item state)` | A pair with the Step proving the removal implication for list term `source`, item term `item` and evaluation environment `state`. | Failure from proof construction. |
| `(b2-removal-disjoin-remove library formula)` | A pair with the Step proving the disjunction-of-removal formula. | Failure from reading the term or constructing the proof. |
| `(b2-removal-arbitrary-hypothesis library formula)` | A pair with the Step proving the arbitrary-hypothesis processor correctness formula. | Failure from reading the term or constructing the proof. |

In `b2-removal-tests`, `prove` is the ordered list of replies to the
proof callback. Each reply is a pair containing the Step and the Library
after the callback, or a failure. When the next reply is missing, the result
is `(:b2-removal-tests-request evidence library)`. Here `evidence` is the
argument to the callback and `library` is the Library in scope at that
call. Pass the extended list of replies with the original inputs to
resume. The traversal visits the true branch before the false branch.

The symbol constants `*b2-removal-ev*`, `*b2-removal-disjoin*`,
`*b2-removal-disjoin2*`, `*b2-removal-conjoin-clauses*`, and
`*b2-removal-remove*` stand for `REMOVE-HYP-EV`, `DISJOIN`, `DISJOIN2`,
`CONJOIN-CLAUSES`, and `REMOVE-EQUAL`. The term constants
`*b2-removal-quoted-true*` and `*b2-removal-quoted-false*` stand for
the quotations of `(QUOTE T)` and `(QUOTE NIL)`.

`(b2-removal-right step)` returns element two of the Step's first literal,
using zero-based indexing. `(b2-removal-assumptions proof signed)` returns
assumption Steps for the ordered list of `(test holds)` pairs. Both can
return a failure. `(b2-removal-tests-request-p result)` recognizes a request
from `b2-removal-tests`.

`(b2-removal-first step)` returns the first literal of a Step, or a failure
if the Step is absent or has an empty clause.
