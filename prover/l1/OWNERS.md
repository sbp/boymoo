# L1 book responsibilities

| Books | Responsibility |
|---|---|
| `lexer`, `counters`, `structural-measures` | Suffix bounds, advancing counters, and ordinal measures for recursive definitions. |
| `reference` | The embedded checker program and the encoding of its proof input. |
| `application`, `lexicographic` | Symbolic evaluation and equations for length-ordered comparisons. |
| `primitive`, `finite-choice` | Primitive dispatch, badge lookup, and finite choice witness construction. |
| `witness`, `guarded`, `recursive` | Choice witnesses, guarded application, and recursive agreement. |
| `rewriting` | Equation indexing, rewriting, and structural induction. |
| `warrant`, `warrant-theorem` | Certificates for warrant constraints and theorems that use them. |
| `books` | Obligation discovery, tactic selection, and certificate assembly. |
| `api`, `open` | The certificate interface, helper naming, and prepared library sessions. |

`prover/l1/ORDER` gives the load order after the shared books. A book may call functions of the shared books and of preceding L1 books.
