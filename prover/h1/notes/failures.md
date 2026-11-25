# Failures in H1

H1 uses the failure values specified in `prover/FAILURES.md`. A generic
failure has an empty message. A fuel failure names the recursion that
exhausted its counter.

| Kind | How H1 uses it |
|---|---|
| `"fuel"` | The caller receives the name of the recursion whose counter ran out. |
| `"unproved"` | Proof search exhausted the tactic. The tests in `h1-book-order-unproved-p`, `h1-book-structure-unproved-p`, `h1-book-field-unproved-p`, `h1-recursion-unproved-p`, `h1-recipes-natural-result-facts`, and `h1-books-unproved` govern subsequent proof attempts. The measure and obligation loops also test this kind. |
| `"candidate-rejected"` | The attempted proof or certificate lacks a required derivation, premise, or entry. `h1-book-termination-termination-entry-visit` advances to the next measure. `h1-books-obligation` records a skip. |

The measure and obligation loops also recognize `"value"` failures
propagated by shared books. A skipped obligation has a separate status
in the worklist output, so an empty failure message still records a
skip.
