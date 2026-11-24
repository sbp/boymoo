# Parity of powers

`proof` is the H1 prover. Terms and Steps have their forms in `prover/sig/proof.md`. The quoted rational one half is `*h1-book-expt-parity-half*` and the quoted integer two is `*h1-book-expt-parity-two*`.

| Function | Arguments in order | Result |
|---|---|---|
| `h1-book-expt-parity-half` | Term | Its product with one half on the left. |
| `h1-book-expt-parity-even` | Term | Integer test for its half. |
| `h1-book-expt-parity-half-at-zero` | `proof`, equality Step with right side zero | Step proving the half of the left side is integer. |
| `h1-book-expt-parity-prove-disjunction` | `proof`, disjunction encoded as an IF term, Step for a disjunct | Step for the disjunction. |
| `h1-book-expt-parity-install-adjacent-parity` | `proof` | Updated prover with the adjacent integer parity lemma. |
| `h1-book-expt-parity-install-negative-one-powers` | `proof` | Updated prover with even and odd powers of negative one. |
| `h1-book-expt-parity-install-base-symmetry` | `proof`, Boolean `odd` | Updated prover with the base negation lemma and recorded formula for that parity. |
| `h1-book-expt-parity-power-on-negative-base` | `proof`, parity label string, premise term | Step for the strict sign under the premise. |
| `h1-book-expt-parity-bound-at-zero-base` | `proof`, Boolean `odd`, equality Step for the base, integer Step for the exponent, parity Step | Step for the zero-base bound. |
| `h1-book-expt-parity-install-sign-for-parity` | `proof`, Boolean `odd` | Updated prover with the strict and weak sign formulas for that parity. |
| `h1-book-expt-parity-install-power-parity` | `proof` | Updated prover with the product formula and the parity and sign lemmas. |

`half` and `even` return their listed results. Every other function can return a failure as its entire result.

`install-base-symmetry`, `install-sign-for-parity`, and `install-power-parity` take a BookProver and register the proved formulas in its theorem and schema indexes.
