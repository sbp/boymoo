# H4 book responsibilities

The load order is given by `prover/h4/ORDER`. Each book can call the shared
books and its predecessors.

| Books | Role |
|---|---|
| `setup` | Package and guard-checking setup. |
| `api-encoding`, `book-encoding` | Rename auxiliary entries and serialize proof steps and entries. |
| `association`, `tactics`, `terms` | Match and normalize terms and build propositional and structural proofs. |
| `book-arithmetic`, `book-division`, `book-measures`, `book-numeric-measures`, `lexicographic` | Prove arithmetic bounds, ordinal measures and termination conditions. |
| `book-choice`, `function-equality`, `warrants`, `badge-table`, `do-loop` | Build proofs about choices, function congruence, badges, warrants and loop evaluation. |
| `book-flatten`, `book-accumulator`, `book-list-types`, `book-printing`, `book-sets` | Prove properties of list maps, accumulators, list members, printing and set equivalence. |
| `book-hints`, `book-tactics`, `book-equivalence`, `book-evaluation`, `book-finite` | Read hints, index rules, search for proofs and discharge evaluation and finite interval goals. |
| `book-order`, `book-compression`, `book-expansion`, `book-inverse` | Prove ordinal comparison, conversion and inversion properties. |
| `book-state`, `book-updates`, `book-hanoi` | Prove facts about list state, updates and disk transfers. |
| `book-alists`, `book-arity`, `book-agreement` | Prove association list properties, list lengths, arities and agreement properties. |
| `book-projections`, `book-projection-sets` | Prove projection equality, list equivalence and membership properties. |
| `recipes`, `book-run`, `api`, `open` | Select proof recipes, produce entries and manage the library and session interfaces. |
