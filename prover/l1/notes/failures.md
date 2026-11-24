# L1 failures

L1 uses `(:failure "failure" "")` for general failures. The kinds below report fuel exhaustion or guide the next proof attempt.

| Kind | Meaning and handling |
|---|---|
| `Fuel` | A recursion reached its counter limit. The message identifies the function. |
| `Unproved` | A proof attempt ran out of applicable steps. `l1-application-unproved-p` recognizes it for witness search. `l1-rewriting-retry-proof-p` also recognizes it for another premise, induction, or certificate attempt. |
| `UnsupportedApplication` | The application or recursive wrapper has a form the tactic does not handle. `l1-recursive-discover-recurrence` tries a different wrapper recipe. `l1-warrant-direct-selection-application` declines the direct selection recipe. `l1-rewriting-retry-proof-p` allows another proof attempt. |
| `NonEqualityArgument` | The choice argument occurs outside an equality test against an independent term. `l1-finite-choice-finite-choice` then declines the finite-choice construction. |
| `MissingWarrantDependency` | A fact, definition, or table entry needed by the warrant recipe is absent. `l1-books-generate-theorem-prepared` uses `l1-books-missing-warrant-dependency-p` to continue with the ordinary theorem tactics. |

The shared operations can return `value` or `key`. The proof and finite-choice predicates recognize `value` for their respective fallbacks. `l1-books-missing-warrant-dependency-p` recognizes `key` for the specialized warrant attempt.
