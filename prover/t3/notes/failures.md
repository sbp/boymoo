# T3 failure kinds

T3 uses the failure form in `prover/FAILURES.md`. Ordinary failures use the
generic kind. Fuel failures name the function whose allowance ran out.

`Unproved` permits another arithmetic decomposition, measure plan or proof
recipe. The tests are `t3-arithmetic-recoverable-failure-p`,
`t3-book-measures-recoverable-failure-p`, `t3-tactics-plan-attempt`,
`t3-api-helper-attempt`, `t3-books-recoverable-proof-failure-p` and
`t3-books-generate-result`.

`Unsupported` lets theorem search try another induction or confines the
failure to the current witness. `t3-book-theorems-unsupported-p`,
`t3-book-witnesses-prove-goals`, `t3-size-doubled-descent` and
`t3-book-measures-prove-clause-search` distinguish it from other failures.
The arithmetic, measure and book fallback tests also accept it.

| Kind | Meaning | Test |
|---|---|---|
| `MalformedLambdaFormals` | The lambda formals cannot be used to select a theorem recipe. | `t3-books-theorem-proof` tries theorem search. |
| `MissingProofInput` | A premise, definition, package entry or subterm needed by a recipe is missing. | `t3-books-recoverable-proof-failure-p` lets `t3-books-theorem-proof` or `t3-books-constrain-proof` try the next approach. |
| `ProofMismatch` | A constructed proof or comparison does not match the recipe's expected form. | `t3-books-recoverable-proof-failure-p` lets the two book entry helpers try another recipe. `t3-api-helper-attempt` checks whether helper admission encountered a duplicate lemma. |

`t3-books-generate-result` gives a skipped obligation the result label
`unproved`. Its fragment has a nonempty reason independent of the failure
message. The proof API returns `nil` when the obligation has no proof.

The fallback tests also recognize the kinds listed for the shared books in
`prover/FAILURES.md`. Those kinds retain their shared meanings when passed to
T3 by a dependency.
