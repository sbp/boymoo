# Constant-index evaluator

A Library and a Step have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. Evidence has the form in `prover/t3/sig/logic.md`.
`name` is a theorem name, `formula` a theorem term, and `template` a term
with the result slot. A substitutions dictionary uses recursive calls as keys
and lists of binding pairs as values, in order of first insertion.

Each function can return a failure from constructing its proof or reading its
arguments. In that case the failure is the entire result.

| Call | Arguments and result |
|---|---|
| `(t3-book-mv-nth-known-application lib term environment function evidence)` | Pair of the evaluator equation Step for `term` and the resulting Evidence. `environment` is the evaluator environment term and `function` the operator symbol. |
| `(t3-book-mv-nth-nth-equivalence lib)` | Library extended with the index-selector equivalence. |
| `(t3-book-mv-nth-nth-equivalence-branch guards through lib target)` | Step for one case of the equality `target` using the list `guards` of evidence Steps and optional intervening Step `through`. Pass `nil` when there is no intervening Step. |
| `(t3-book-mv-nth-recurrence lib name formula)` | Pair of the recurrence theorem entry and the Library with its auxiliary lemma. |
| `(t3-book-mv-nth-recurrence-leaf raw tests lib premise index-result measure formula template substitutions)` | Pair of the branch Step and the updated substitutions dictionary. `raw` is the branch value, `tests` the signed tests, `premise` the premise Step, and `index-result` and `measure` are terms. |
| `(t3-book-mv-nth-correctness lib name formula)` | Optimization theorem entry. |
| `(t3-book-mv-nth-correctness-leaf value tests lib)` | Step for the evaluator result at branch term `value` under the signed `tests`. |

The term constants are `*t3-book-mv-nth-recurse*`, `*t3-book-mv-nth-optimize*`,
`*t3-book-mv-nth-recurrence*`, `*t3-book-mv-nth-env*`, `*t3-book-mv-nth-n*`,
`*t3-book-mv-nth-term*` and `*t3-book-mv-nth-nth*`.
