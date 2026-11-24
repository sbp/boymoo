# B2 book responsibilities

| Responsibility | Books |
|---|---|
| Library preparation and proof entry assembly | `api-loader`, `api`, `open`, `api-entries`, `reuse` |
| Proof search, rewriting, and induction | `tactics`, `search`, `structural`, `measures`, `bounds`, `equivalences`, `completions` |
| Theorem and witness dispatch | `recipes`, `shape-recipes`, `next-recipes`, `witnesses` |
| List operations and ordering | `association`, `bags`, `butlast`, `character-lists`, `folds`, `lexicographic`, `list-properties`, `lists`, `removal`, `reversal`, `sort-order`, `sorting`, `strict-lexicographic`, `strict-order` |
| Records and name lookup | `keywords`, `record-extensionality`, `record-update`, `records` |
| Evaluators, terms, and projection | `delimiters`, `evaluator`, `mv-evaluation`, `projections`, `pseudo-terms`, `substitution`, `term-trees`, `xdoc` |
| Arithmetic and result types | `algebra`, `arithmetic`, `exponent-types`, `fraction-reduction`, `logand`, `meta-cancel`, `meta-fold`, `numeric-types`, `pair-products`, `powers`, `products`, `radix`, `rational-order`, `reciprocal`, `scaling`, `signed-bitwise` |
| Rounding, quotients, and remainders | `floor-intervals`, `floor-ranges`, `floor-translation`, `quotient-algebra`, `quotient-interval`, `quotients`, `remainder-properties`, `rounding-relations`, `truncate-intervals` |
| Pathname measures and comparisons | `pathnames` |

`prover/b2/ORDER` specifies the dependency order within B2. The shared
books' certificate is included through `descent`. The B2 build and proof
check commands are in `prover/b2/README.md`.
