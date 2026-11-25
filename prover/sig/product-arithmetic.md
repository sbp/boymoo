# Integer product proofs

`lib` is a SliceLibrary or BookLibrary, in the Library form from
`prover/sig/library.md`. Terms and Steps use the forms in `prover/sig/proof.md`.
`types` is a list of Steps proving integrality. Each call can return a failure
in place of its listed result. A result written `(cons value lib)` contains
the value and the Library after any additions.

| Function | Arguments in order | Result |
|---|---|---|
| `product-arithmetic-product` | `a`, `b` (terms) | The product term |
| `product-arithmetic-conjunction` | `terms` (list of terms) | Right-nested conjunction term |
| `product-arithmetic-conjoin` | `lib`, `proofs` (list of Steps) | Step proving their right-nested conjunction |
| `product-arithmetic-product-form` | `lib`, `term` | Step equating a term with its right-associated product of ordered factors |
| `product-arithmetic-product-equal` | `lib`, `left`, `right` (terms) | Step equating two products, or `different-normal-forms` for different normalized factors |
| `product-arithmetic-one-product` | `lib`, `value` (term), `types` | `(cons step lib)` proving multiplication by one |
| `product-arithmetic-positive-nonzero` | `lib`, `value` (term), `proof` (positivity Step) | Step proving nonzero value |
| `product-arithmetic-zero-product-lemma` | `lib` | Library with the product-zero lemma |
| `product-arithmetic-product-zero` | `lib`, `value` (term), `integral` (Step) | `(cons step lib)` proving multiplication by zero |
| `product-arithmetic-minus-product-lemma` | `lib` | Library with the product-negation lemma |
| `product-arithmetic-product-difference` | `lib`, `a`, `b`, `factor` (terms), `types` | `(cons step lib)` proving distribution over a difference |
| `product-arithmetic-positive-product` | `lib`, `a`, `b` (terms), `types`, `pa`, `pb` (positivity Steps) | `(cons step lib)` proving a positive product |
| `product-arithmetic-product-order-lemma` | `lib` | Library with the strict product order lemma |
| `product-arithmetic-product-order` | `lib`, `a`, `b`, `factor` (terms), `types`, `strict`, `positive-factor` (Steps) | `(cons step lib)` lifting strict order through multiplication |
| `product-arithmetic-reflect-positive-product` | `lib`, `value`, `factor` (terms), `types`, `positive-term`, `positive-factor` (Steps) | `(cons step lib)` reflecting positivity from the product to `value` |
| `product-arithmetic-reflect-product-order` | `lib`, `a`, `b`, `factor` (terms), `types`, `strict`, `positive-factor` (Steps) | `(cons step lib)` reflecting strict order from two products |
