# Failures in H3

An H3 tactic that finishes without a proof can return `"unproved"`.
`h3-book-tactics-try-tactics` and `h3-book-witness-try-formulas` use
`h3-rewrite-unproved-p` to recognize that kind and try another tactic or
witness.
`"fuel"` identifies recursion that exhausts its counter. Its message
names the function. All other H3 failure messages are empty.
See [the shared failure convention](../../FAILURES.md).

| Kind | Condition | Functions that test it |
|---|---|---|
| `"malformed-tactic-input"` | A slice tactic cannot read a label or use a term or proof step in the required form. | `h3-api-theorem-entry-using` tries the book tactics. |
| `"missing-proof-data"` | A slice tactic needs a declaration, rule, or item of evidence that is absent. | `h3-api-theorem-entry-using` tries the book tactics. |
| `"proof-mismatch"` | A proof step does not establish the clause or term required by the tactic. | `h3-api-theorem-entry-using` tries the book tactics. `h3-book-tactics-induction-attempt` tries another induction opening. `h3-book-descent-retryable-p` lets the caller continue the measure search. |
| `"different-normal-forms"` | The two sides of an arithmetic comparison have different normal forms. | `h3-api-theorem-entry-using` tries the book tactics. `h3-book-tactics-solve-theorem-search` continues from additive reasoning to rewriting. `h3-book-translation-retryable-p` lets modulus translation try another displacement. |
| `"wrong-sum-arity"` | A dividend sum that the rational-ratio recipe would expand has a number of operands other than two. | `h3-book-translation-retryable-p` lets modulus translation try another displacement. |

H3 also recognizes the shared failure kinds `"value"`, `"key"`,
`"assertion"`, `"index"`, `"type"`, and `"attribute"` at recovery
points. Where a caller has no alternate tactic for the reason, H3
creates `(:failure "failure" "")`.
