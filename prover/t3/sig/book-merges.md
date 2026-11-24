# Merge and alternating split laws

`lib` is a Library as in `prover/sig/library.md`. Terms and Steps use the
forms in `prover/sig/proof.md`. `formula` is a theorem term, `name` is its
symbol, and `pairs` is a list of two-element `(variable term)` lists.

A Merge has the form `(:t3-merge lib formula x y decision call measure
substitutions)`. `x` and `y` are the cons tests, `decision` is the comparison
of their heads, `call` is the merge call, and `measure` is the sum of the
argument lengths. `substitutions` contains the two recursive substitutions,
first advancing `X`, then advancing `Y`. Use the constructor below and
the accessors named `t3-book-merges-merge-` followed by the field name.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t3-book-merges-occurrences sequence)` | Occurrence-count term for `E` in the given term. | None. |
| `(t3-book-merges-proper sequence)` | `TRUE-LISTP` term for the given term. | None. |
| `(t3-book-merges-proper-args x y)` | Conditional conjunction of the `TRUE-LISTP` tests on the two terms. | None. |
| `(t3-book-merges-hypothesis lib formula smaller measure pairs decreases)` | Induction hypothesis Step at `pairs`, discharged with the decrease Step `decreases` from `measure` to `smaller`. | A construction failure. |
| `(t3-book-merges-merge-init lib formula)` | Merge for the Library and formula. | None. |
| `(t3-book-merges-merge-remaining merge branch evidence)` | Induction hypothesis Step for branch index 0 or 1. `evidence` is the ordered list of assumption Steps. | A construction failure. |
| `(t3-book-merges-merge-prove merge base recursive implication-goal)` | Induction Step, or a request for a callback result. `implication-goal` is Boolean. | A construction or callback failure. |
| `(t3-book-merges-through lib template equation)` | Equality Step applying the unary term template to both sides of the given equality Step. Mark the argument with `*proof-result*`. | A construction failure. |
| `(t3-book-merges-sort-induction lib formula base recursive implication-goal)` | `(cons step lib)` with the sort induction Step and Library including any auxiliary entries, or a request for a callback result. `implication-goal` is Boolean. | A construction or callback failure. |
| `(t3-book-merges-proper-evens lib)` | Step proving that `EVENS` returns a true list. | A construction failure. |
| `(t3-book-merges-merge-count lib name formula)` | `(cons entry lib)` with the merge occurrence-count theorem. | A construction failure. |
| `(t3-book-merges-split-count lib name formula)` | `(cons entry lib)` with the alternating split occurrence-count theorem. | A construction failure. |
| `(t3-book-merges-sort-count lib name formula)` | `(cons entry lib)` with the merge-sort occurrence-count theorem and the Library including any auxiliary entries. | A construction failure. |
| `(t3-book-merges-sort-proper lib name formula)` | `(cons entry lib)` with the merge-sort true-list theorem and the Library including the merge lemma and any length lemmas. | A construction failure. |

In the two induction calls, `base` and `recursive` are alists from argument
lists to returned Steps or failures, with entries `(args . result)`. Merge base
arguments are `(branch evidence)` and recursive arguments are `(branch
evidence induction-step)`. Sort base arguments are `(equation)` and recursive
arguments are `(equation parent evens odds)`, all Steps. A missing reply returns
`(:t3-book-merges-call kind args lib)`, where `kind` is `:base` or `:recursive`,
and `lib` is the Library at that call. Supply the result in the appropriate
alist and call the induction function again with the same inputs. Merge
visits recursive branches 0 and 1, then base branches 1 and 0. Sort visits
the recursive branch and then the base branch.

The prover symbols are `*t3-book-merges-merge*`, `*t3-book-merges-sort*`,
`*t3-book-merges-order*`, `*t3-book-merges-e*`, `*t3-book-merges-merge-count*`,
and `*t3-book-merges-split-count*`. The imported symbols are also available as
`*t3-book-merges-occurrences*`, `*t3-book-merges-evens*`, and
`*t3-book-merges-true-listp*`.
