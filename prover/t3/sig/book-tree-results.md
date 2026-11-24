# Tree results

`lib` is a Library with the T3 proof rules for its dispatch tag. Formulas are
terms and proofs are Steps in the forms in `prover/sig/proof.md`.
A missing proof is `nil`. A failure is the entire result.

| Call | Result | Failure |
|---|---|---|
| `(t3-book-tree-results-identical-branches lib value)` | Equality Step reducing conditional term `value` to its common branch. | A failure for a term without identical branches or from constructing the proof. |
| `(t3-book-tree-results-tree-cons lib formula)` | Step for the tree recognition equality on a cons, or `nil` if it does not apply. | A failure from constructing the proof. |
| `(t3-book-tree-results-proper-list-boolean lib)` | Library with the lemma that the proper-list recognizer returns a Boolean. | A failure from constructing or adding the lemma. |
| `(t3-book-tree-results-swap-boolean-tests lib opened types)` | Step equating the two orders of the Boolean tests. `opened` is the starting equality Step and `types` contains the two Boolean type Steps in test order. | A failure from constructing the proof. |
| `(t3-book-tree-results-swap-boolean-tests-common-result first-holds second-holds lib body first second reverse opened types)` | Step for one choice of the two signed tests in `swap-boolean-tests`. `body` and `reverse` are the conditional terms in the two orders. | A failure from constructing the proof. |
| `(t3-book-tree-results-event-cons lib formula)` | Pair `(cons step lib)` with the pseudo-event recognition equality Step or `nil`, and the Library at the end of the attempt. The proper-list Boolean lemma is retained if the attempt added it. | A failure from constructing the proof or adding the lemma. |
| `(t3-book-tree-results-instantiate-constructor lib name values)` | Constructor fact Step for prover symbol `name`, instantiated with list `values` in formal order. | A failure from finding, reading or instantiating the fact. |
| `(t3-book-tree-results-same-choice lib equation wanted test)` | Step showing equality to term `wanted` by reducing both sides under term `test`, true first, or `nil` for different results. | A failure from constructing the proof. |
| `(t3-book-tree-results-tree-tag lib formula)` | Step for a tree recognition equality on a tag constructor, or `nil` if its choices differ. | A failure from constructing the proof. |
| `(t3-book-tree-results-rendered-tree lib formula)` | Step for a tree recognition equality on a supported constructor or a tag alias, or `nil` if it does not apply. | A failure from constructing the proof. |

The prover-symbol constants have the prefix `*t3-book-tree-results-` and
suffixes `tree*`, `tree-list*`, `tree-tag*`, `make-tag*`, `cons-rule*`,
`tag-rule*`, `keywordp*`, `symbolp*` and `pseudo-event*`.

`(t3-book-tree-results-rendered-tree-in-book book formula)` takes the
book proof context from `prover/t3/sig/book-values.md` and uses its package
visibility for the alias test. The result and failures are those of
`rendered-tree`, which uses the visible packages of the ground theory.
