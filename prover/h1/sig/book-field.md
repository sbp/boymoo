# Field proofs

`proof` is the H1 Prover from `tactics`. `normalizer` is the Algebra object
from `book-arithmetic`. Terms and Steps have the forms in `prover/sig/proof.md`.
`tests` is an ordered list of `(term holds)` pairs, with `t` for a true test and
`nil` for a false test. Evidence Steps are used in list order.

| Call | Result | Failure |
|---|---|---|
| `(h1-book-field-fixed term)` | The `FIX` application to `term`. | — |
| `(h1-book-field-reciprocal term)` | The `UNARY-/` application to `term`. | — |
| `(h1-book-field-require normalizer literal)` | `(cons step normalizer)` with the Step for `literal` and the resulting Algebra after its context lookup. | `Unproved` for missing evidence, or a failure from lookup. |
| `(h1-book-field-remember normalizer steps)` | The updated Algebra after inserting and binding each given Step in order. | A failure from reading or binding a Step. |
| `(h1-book-field-install-field proof)` | The Prover with the field lemmas and rules installed in order. | A failure from proof construction. |
| `(h1-book-field-field-normalizer proof tests)` | A new Algebra, with its context initialized from the tests and then extended by the field and sign evidence in encounter order. | A failure from constructing the Algebra or its evidence. |
| `(h1-book-field-field-proof proof formula)` | A Step proving `formula`. | `Unproved` if the tactic cannot close the proof, or a failure from proof construction. |

`*h1-book-field-inverse-unique*` is the prover symbol `H1-INVERSE-UNIQUE`.
Updates to the Algebra context retain the position of an existing
evidence key.
