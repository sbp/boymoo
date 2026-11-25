# Function recognizers

A Library and a Step have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. The constant `*t3-book-function-terms-arity*` is the
symbol `ARITY`. A facts dictionary uses terms as keys and Steps as values,
in discovery order. Setting an existing key keeps its position.

Each function can return a failure from constructing its proof or reading its
arguments. In that case the failure is the entire result.

| Call | Arguments and result |
|---|---|
| `(t3-book-function-terms-theorem-from lib name target facts)` | Step for `target` from the matching named theorem and the list `facts` of premise Steps. |
| `(t3-book-function-terms-fn-from-term lib name formula)` | Entry for the theorem extracting a function from a term. |
| `(t3-book-function-terms-lambda-components lib typed)` | Facts dictionary for the conjuncts obtained by expanding the first literal of Step `typed`. |
| `(t3-book-function-terms-fn-from-lambda lib name formula)` | Entry for the theorem recognizing a lambda as a function. |
| `(t3-book-function-terms-pseudo-fn-from-term lib name formula)` | Entry for the theorem extracting a pseudo-function from a term. |
| `(t3-book-function-terms-nonnil-integer lib typed)` | Step that the argument of the integer predicate in Step `typed` is non-nil. |
| `(t3-book-function-terms-symbol-application lib target symbol arguments not-quote arity)` | A Step for recognizer term `target` using Steps for the head's symbol type, the argument types, exclusion of quotation and the arity equality. |
| `(t3-book-function-terms-from-function lib name formula)` | Pair of the theorem entry for constructing an application from a function and the resulting Library. |
| `(t3-book-function-terms-finish lib name formula proof)` | Entry for `name` with the implication `formula` discharged using Step `proof`. |
| `(t3-book-function-terms-fact-table steps facts)` | Facts dictionary after setting each first literal in `steps` to its Step in order. |
| `(t3-book-function-terms-fact-at facts term)` | Value at the key `term` in ordered table `facts`, or `missing-proof-input`. |
