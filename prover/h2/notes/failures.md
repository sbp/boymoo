# Failures in H2

H2 uses the generic `(:failure "failure" "")` from `prover/FAILURES.md` for
a failure that carries no search decision. The following kinds carry
a decision or an exhausted recursion counter.

| Kind | Meaning | Consumer |
|---|---|---|
| `fuel` | A recursion reached the end of its explicit counter. The message names the function that stopped. | The value propagates to the caller. |
| `unproved` | A tactic exhausted its proof candidates or its rewriting budget. | `h2-books-unproved-p` inspects this kind for further searches and certificate construction. `h2-witnesses-unproved-p` advances the witness search. `h2-api-special-fallback-p` allows the general theorem tactic to run. `h2-book-recipes-output` and `h2-compression-lookup-output` can preserve it with the updated proof. |
| `tactic-inapplicable` | The specialized theorem tactic could not satisfy a term, rule, table, or primitive-evaluation prerequisite. | `h2-api-special-fallback-p` starts the general theorem tactic from a fresh trial. |
| `arithmetic-inapplicable` | Numeric evidence is unavailable or the two sum normal forms differ. | `h2-calculation-inapplicable-p` selects another arithmetic candidate or returns `nil`. `h2-api-special-fallback-p` allows the general theorem tactic to run if this kind reaches the interface. |

A specialized theorem attempt can receive a failure from a shared
operation. `h2-api-special-fallback-p` recognizes the shared kinds
`assertion`, `key`, `value`, `index`, `type`, `encoding`, `decoding`, and
`translating` for its retry. `h2-calculation-inapplicable-p` and
`h2-ranges-inapplicable-p` recognize the shared `value` kind for
arithmetic candidates. In `books.lisp`, `h2-books-selector-rule`,
`h2-books-finite-rule`, and `h2-books-termination-ordinality` interpret
shared failures while trying decrease and order proofs.
