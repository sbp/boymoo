# Singleton-clause processors

A Library and a Step have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. Each function can return a failure from constructing its
proof or reading its arguments. In that case the failure is the entire result.

| Call | Arguments and result |
|---|---|
| `(t3-book-clause-processors-empty-type lib predicate world)` | Step for the given type predicate on the quoted empty list in the world term `world`. |
| `(t3-book-clause-processors-pair-type lib predicate value world head tail)` | Step for the given type predicate on constructor term `value` from the Steps `head` and `tail` for its two components. |
| `(t3-book-clause-processors-marker-types lib term world facts)` | Two Steps for the marker term's well-formedness and use of permitted functions. `facts` is an insertion-ordered table from terms to Steps. |
| `(t3-book-clause-processors-wellformed lib name formula)` | Pair of the well-formedness theorem entry and the resulting Library. |
| `(t3-book-clause-processors-eval-application lib term environment operator)` | Evaluation equation Step for the application of the operator symbol in `term` and the given evaluator environment term. |
| `(t3-book-clause-processors-evaluated lib equation environment)` | Evaluation equation Step obtained by applying the evaluator to both sides of Step `equation`. |
| `(t3-book-clause-processors-false-disjunction lib)` | Library extended by the two false-prefix lemmas in their dependency order. |
| `(t3-book-clause-processors-false-disjunction-branch value tests lib right hypothesis)` | Step for the disjunction branch term `value` given signed `tests`, the right evaluation term, and the Step `hypothesis` that the left evaluation is false. |
| `(t3-book-clause-processors-marker-false lib marker environment)` | Step that the marker term evaluates to false in the given evaluator environment term. |
| `(t3-book-clause-processors-processor-correct lib name formula)` | Pair of the processor correctness theorem entry and the resulting Library. |

The term constants use the prefix `*t3-book-clause-processors-`. Their suffixes
are `process*`, `ev*`, `flag-is*`, `conjoin-clauses*`, `conjoin*`,
`disjoin*`, `disjoin2*`, `disjoin-list*`, `logic-nested*`, `real-nested*`,
`functions-nested*`, `logicp*`, `arities*`, `qtrue*` and `qfalse*`.
