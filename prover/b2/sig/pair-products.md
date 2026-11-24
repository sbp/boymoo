# Compact pair proofs

`lib` is the tactic library. Terms and Steps use the forms in `prover/sig/proof.md`. Each call may return a failure in place of the listed result.

| Call | Arguments and result |
|---|---|
| `(b2-pair-products-cons-cases lib a b replies)` | Step joined from the construction cases of pair argument terms `a` and `b`. `replies` is an alist with `(constructed facts)` keys and Step or failure values. At the first missing reply the result is `(:b2-pair-products-cons-cases constructed facts)`. Supply that reply and repeat the call. |
| `(b2-pair-products-pair-size lib formula)` | Step proving the pair size formula. |
| `(b2-pair-products-pair-reconstruction lib formula)` | Step proving the reconstruction formula. |
| `(b2-pair-products-pair-equality lib formula)` | Step proving the pair equality formula. |
| `(b2-pair-products-pair-theorem lib name formula)` | Step proving the pair theorem given its symbol `name` and statement term `formula`. |

In a construction case, `constructed` is the constructed term and `facts` is the ordered list of Steps for that branch.

The constants are `*b2-pair-products-pair*`, `*b2-pair-products-pairp*`, `*b2-pair-products-tag*`, `*b2-pair-products-selectors*`, `*b2-pair-products-rebuild*`, `*b2-pair-products-equality*`, `*b2-pair-products-size*`, `*b2-pair-products-tag-cons*` and `*b2-pair-products-pair-theorems*`. `*b2-pair-products-selectors*` is an association list in `CAR`, `CDR` order. `*b2-pair-products-pair-theorems*` lists the supported theorem symbols.
