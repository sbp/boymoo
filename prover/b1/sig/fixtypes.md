# Product, lookup and clause processor proofs

Each call takes a Library `lib` and a term `formula` in that order. The
Library, terms and Steps use the representations in `prover/sig/library.md`
and `prover/sig/proof.md`. Each call can return a failure from reading the
formula or constructing a proof. A failure is the entire result.

| Call | Result |
|---|---|
| `(b1-fixtypes-product-selector lib formula)` | Step for the `CAR` or `CDR` of a compact product cell. |
| `(b1-fixtypes-product-reconstruction lib formula)` | Step for reconstructing a product from its two fields. |
| `(b1-fixtypes-product-equality lib formula)` | Step for comparing a product with a compact product cell. |
| `(b1-fixtypes-product-against-cons lib formula)` | Step for comparing a compact product cell with a `CONS`. |
| `(b1-fixtypes-product-size lib formula)` | `(cons step lib)` with the Step for the bounds on the sizes of the fields, and the Library with any numeric lemmas used by the proof. |
| `(b1-fixtypes-product-empty lib formula)` | Step for the fields of an atomic compact product cell. |
| `(b1-fixtypes-tag-implies-cons lib formula)` | Step showing that a recognized tag requires a cons. |
| `(b1-fixtypes-lookup-result-type lib formula)` | Step for the Boolean or symbol-list type of a lookup result. |
| `(b1-fixtypes-mv-nth-of-cons lib formula)` | Step for selecting a multiple value from a cons. |
| `(b1-fixtypes-split-result-proper lib formula)` | Step for the proper list returned as one component of a list split. |
| `(b1-fixtypes-identity-processor-wellformed lib formula)` | Step for well-formed output of the identity clause processor. |
| `(b1-fixtypes-identity-processor-correct lib formula)` | Step for correctness of the identity clause processor. |

The term constants are `*b1-fixtypes-hard-error*`, `*b1-fixtypes-mv-nth*`,
`*b1-fixtypes-symbol-listp*`, and `*b1-fixtypes-true-listp*`.
