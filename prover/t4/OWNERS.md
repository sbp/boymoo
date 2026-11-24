# Book responsibilities

The table groups the T4 books by the proof operations they supply.
`prover/t4/ORDER` gives the order of certification and dependencies.

| Books | Responsibility |
|---|---|
| `bookwitness`, `witness`, `evaluator` | Construct witnesses for constraints with constant candidates, selectors, and evaluators. |
| `ranges`, `structural`, `ordinals`, `lexicographic`, `application`, `unification` | Prove ordinality and descent of measures for recursive definitions. |
| `division`, `algebra`, `order`, `field`, `ordered` | Prove numeric identities, bounds, sign conditions, and order comparisons. |
| `records`, `record-laws`, `hash-lists`, `treeorder` | Prove properties of record updates, lookup tables, membership, and tree order. |
| `relations`, `results`, `syntax-lists`, `list-types` | Prove relation laws and properties of returned values and lists. |
| `evaluation`, `mvmeta`, `printing` | Prove evaluator equations, projection laws, and character-list properties. |
| `recognizers`, `constructors` | Prove implications, equations, and result properties for constructors and recognizers. |
| `booklogic` | Index the admitted facts and run theorem search with the tactic context. |
| `bookrun`, `slice` | Select proof obligations, generate proof entries, and assemble the required auxiliary entries. |
| `api`, `open` | Read proof requests, prepare library sessions, and return answers. |
