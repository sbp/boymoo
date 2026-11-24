# Occurrence counts

`lib` is a Library. Steps and terms use the forms in `prover/sig/proof.md`.
Each function can return a failure from reading a term or building a proof.
`nil` is the result of a recipe that does not recognize the given argument.

| Call | Arguments and result |
| --- | --- |
| `(t3-book-occurrences-natural-count lib call variable)` | Library, numeric fold call term and its recursive variable. Returns a Step proving the count natural. |
| `(t3-book-occurrences-count-same-key lib formula count remove member key variable)` | Library, formula term, count, removal and membership function symbols, key term and recursive variable. Returns the count equation Step for equal keys or `nil`. |
| `(t3-book-occurrences-after-removal lib formula solve)` | Library, formula term and the table of solver replies described below. Returns the count equation Step, `nil` or a solver request. |
| `(t3-book-occurrences-natural-count-leaf n value tests lib recursive premise)` | Natural-number fuel, leaf term, signed test list, Library, recursive call term and induction Step. Returns a naturality Step. Pass `1000000` for initial fuel. |
| `(t3-book-occurrences-natural-count-case holds lib call test recursive premise)` | Boolean branch, Library, fold call term, branch test term, recursive call term and induction Step. Returns the branch naturality Step. |
| `(t3-book-occurrences-count-same-key-reduced tests lib removed lhs occurs rhs current)` | List of evidence Steps, Library, removal call, left side, membership call, right side and original count call. Returns the list of two reduced equality Steps, in left and right order. |

`solve` is an association list of `(goal . answer)` entries where the answer
is a Step, `nil`, or a failure. Start with an empty table. When the recipe
reaches a goal absent from the table, it returns
`(:t3-book-occurrences-solve goal)`. The caller runs the solver on that goal
and calls the recipe again with the answer in the table, including when the
answer is `nil`. `t3-book-occurrences-solve-request-p` recognizes a solver
request and `t3-book-occurrences-solve-request-goal` extracts its goal.
