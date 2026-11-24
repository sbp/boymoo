# H1 book responsibilities

| Book | Responsibility |
|---|---|
| `arithmetic` | Arithmetic identities and proof requests |
| `propositions` | Propositional inferences and simplification |
| `tactics` | Inference rules, search contexts, and proof search |
| `book-arithmetic` | Algebraic normalization and equality |
| `recursion` | Recursive instances and structural induction |
| `book-order` | Sign and comparison proofs |
| `book-structure` | List and association proofs |
| `recipes` | Proof construction for recognized theorem forms |
| `book-field` | Field normalizers and arithmetic transformations |
| `book-substitution` | Structural substitution and result types |
| `book-cofactors` | Cofactor and measure proofs |
| `book-expt` | Powers and exponent induction |
| `book-expt-sum` | Addition of exponents |
| `book-fraction` | Numerators, denominators, and fraction identities |
| `book-modulo` | Quotient and remainder proofs |
| `book-euclid` | Euclidean induction and linear combinations |
| `book-expt-composition` | Composition of powers |
| `book-expt-order` | Bounds and monotonicity of powers |
| `book-termination` | Evidence under rulers and termination measures |
| `book-expt-parity` | Parity of powers |
| `book-list-size` | Length and structural count bounds |
| `book-rewrite-equal` | Correctness of equality substitution |
| `book-scan` | Bounds for scans and difference positions |
| `book-witness` | Construction of witnesses for constraints |
| `book-disjoin` | Disjunction and truth-fold proofs |
| `book-resize` | Length and indexing of resized lists |
| `book-trigger` | Rewrite trigger selection and correctness |
| `books` | Book proof worlds, obligations, and certificates |
| `api-engine` | Admission of statement lines and proof export |
| `api` | Single-statement proof interface |
| `open` | Prepared library and ordered session calls |

The books use the shared definitions through `descent` and load in
`prover/h1/ORDER`.
