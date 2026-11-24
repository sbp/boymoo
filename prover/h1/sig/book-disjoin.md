# Disjunction proofs

`proof` is the H1 proof world used by the book tactics. Terms and Steps
have the forms in `prover/sig/proof.md`. Test pairs are ordered
`(term holds)` lists, with `t` for true and `nil` for false.

| Call | Result | Failure |
|---|---|---|
| `(h1-book-disjoin-install-disjunctions proof)` | The proof world with the disjunction lemmas, truth fold definition and measure, and indexed formulas installed in order. | A failure from proof construction or registration. |
| `(h1-book-disjoin-truth value)` | The term `(IF value 'T 'NIL)`. | — |
| `(h1-book-disjoin-eval-quoted proof term)` | A Step reducing the evaluator applied to the quoted term. | A failure from proof construction. |
| `(h1-book-disjoin-eval-constructed proof evaluator-rule term)` | A Step from evaluator constraint number `evaluator-rule` with the projections of the nested cons term reduced in order. | A failure from proof construction. |
| `(h1-book-disjoin-disjoin2-value proof)` | A Step for the truth of the evaluated binary disjunction. | A failure from proof construction. |
| `(h1-book-disjoin-disjoin2-value-leaf value tests proof target)` | A Step equating the truth of the evaluated leaf value to the target term under its ordered tests. | A failure from proof construction. |
| `(h1-book-disjoin-define-truth-fold proof)` | The proof world with the truth fold definition and its measure entry appended in order. | A failure from proof construction or registration. |
| `(h1-book-disjoin-any-evaluated proof terms cons-step)` | A Step opening the truth fold of the evaluated term list using the given cons or noncons evidence Step. | A failure from proof construction. |
| `(h1-book-disjoin-evaluated-disjoin proof)` | A Step equating the truth of an evaluated disjunction to the truth fold of its evaluated arguments. | A failure from proof construction. |
| `(h1-book-disjoin-evaluated-disjoin-start equation proof formula)` | A Step rewriting the right side of reflexivity on the left side of the equality term `formula` by the given equation Step. | A failure from proof construction. |
| `(h1-book-disjoin-prove-rewrite-transfer proof)` | A Step transferring a true evaluated disjunction through expression substitution. | A failure from proof construction. |
| `(h1-book-disjoin-falsity-of-member proof)` | A Step proving that an evaluated member of a false disjunction is false. | A failure from proof construction. |

`*h1-book-disjoin-disjoin*`, `*h1-book-disjoin-disjoin2*`,
`*h1-book-disjoin-member*` and `*h1-book-disjoin-any*` are the prover
symbols `DISJOIN`, `DISJOIN2`, `MEMBER-EQUAL` and
`H1-ANY-EVALUATED-TRUE`. `*h1-book-disjoin-quoted-false*` and
`*h1-book-disjoin-quoted-true*` are the quoted terms for the quotations
of `NIL` and `T`, respectively.
