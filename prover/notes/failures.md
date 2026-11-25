# T1 failure kinds

T1 uses tagged failures. The generic failure ends the current operation.
Predicates tell a tactic whether it can try another proof.
[Failure format](../FAILURES.md) · [Predicates](../terms.lisp)

| Kind | Meaning | Test |
|---|---|---|
| `unproved` | The tactic could find no proof. | `terms-unproved-p` recognizes it. For example, `proof-search-prove-fact` tries the next candidate and `book-proofs-book-prover-prove` rolls back auxiliary entries and records a skipped obligation. |
| `missing-measure-ordinality` | The chosen measure still needs a proof that its value is an ordinal. | `book-proofs-book-termination` tests this failure specifically and retries if measure normalization changes a measure. `terms-unproved-p` also recognizes it. |
| `invalid-proof-arity` | A call, binding or proof obligation has the wrong number of fields. | `terms-proof-fallback-p` recognizes it where a tactic can try another proof, including `book-proofs-earlier-decrease-prepare`. |
| `different-normal-forms` | Normalization of the two sides gives different terms. | `terms-proof-fallback-p` recognizes it. `proof-search-reduced-equality` can continue with another tactic. |
| `fuel` | A recursion exhausts its iteration counter. | `failure-p` recognizes the failure. The message names the recursion. |

`terms-proof-fallback-p` also accepts the shared `value` failure.
`strsplit-proofs-string-tactic` and `book-proofs-theorem-entry`
recognize the shared `key` failure when a required definition or
fact is missing.
