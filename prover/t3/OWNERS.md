# T3 book inventory

`prover/t3/ORDER` gives the dependency order. A book may call the shared
books and the T3 books that precede it in that order. Each book's
definitions and result forms are described in the corresponding file
under `prover/t3/sig/`.

| Purpose | Books |
|---|---|
| Primitive proofs and arithmetic | `book-lemmas`, `logic`, `arithmetic`, `rational`, `rational-order`, `book-numeric-order`, `book-equivalence`, `book-values` |
| Measures and bounds | `book-halves`, `scan`, `size`, `formatting`, `list-bounds`, `quotient`, `trees`, `digit-capacity`, `printing`, `name-bounds`, `genvar`, `tactics`, `book-measures` |
| Result and recognizer proofs | `book-spines`, `book-associations`, `book-character-lists`, `book-indexed-calls`, `book-projections`, `book-strings`, `book-substitution`, `book-term-collections`, `book-remove-progn`, `book-symbol-tables`, `book-term-order`, `book-tree-results`, `book-function-terms`, `book-world` |
| Sorting and permutations | `book-occurrences`, `book-permutations`, `book-counterexamples`, `book-merges`, `book-sorted-lists` |
| Evaluators and witnesses | `book-defpun`, `book-evaluators`, `book-lambdas`, `book-mv-nth`, `book-clause-processors`, `book-witnesses` |
| Search and proof interfaces | `book-theorems`, `book-recipes`, `books`, `api`, `open` |
