# B1 book responsibilities

`prover/b1/ORDER` lists each B1 book in dependency order. The following
groups describe the parts of the prover implemented by those books.

| Responsibility | Books |
|---|---|
| Inference, records, and search | `logic`, `records`, `induction`, `search` |
| Numeric identities, bounds, and types | `arithmetic`, `integer`, `quotient`, `reciprocal`, `powers`, `total-order`, `division`, `floor`, `parity`, `scaling`, `bits`, `bitwise`, `modular`, `monotone`, `bit-length`, `conjunction`, `floor-sum`, `integrality`, `reduced`, `mod-expt`, `numerators` |
| Recursive measures and induction on ordered arguments | `measures`, `lexical` |
| List and set properties | `permutation`, `predicates`, `revappend`, `list-types`, `membership`, `list-sets`, `set-laws`, `abstract-lists` |
| Data structures, evaluators, and specialized term recipes | `structures`, `arrays`, `evaluators`, `fixtypes`, `printing`, `typed-alists`, `array-scan`, `clause-processors`, `fixer-laws`, `xdoc-types`, `bit-types`, `mismatch` |
| Recipe dispatch, certificates, and sessions | `witnesses`, `shapes`, `theorems`, `generate`, `api`, `open` |
