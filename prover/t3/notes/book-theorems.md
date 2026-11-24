# Theorem search

The theorem index records facts and rewrites in insertion order.
Measure and witness recipes can replace its Library with
`t3-book-theorems-with-library`, preserving the package declarations
used by quoted primitive computations.

`t3-book-theorems-quick-result` and `t3-book-theorems-prove-formula`
return a Step, an optional Step, or a failure in the car and the
search with its remaining allowance in the cdr. Induction uses stored
recursive-call summaries for definitions in scope.
