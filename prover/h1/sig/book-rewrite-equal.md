# Evaluation under equal substitution

`proof` is an H1 Prover. Terms and Steps have the forms in
`prover/sig/proof.md`. A constraint index is an integer.

| Call | Result | Failure |
|---|---|---|
| `(h1-book-rewrite-equal-evaluated term)` | The term `(EQEV term ALIST)`. | — |
| `(h1-book-rewrite-equal-evaluated-list terms)` | The term `(EQEV-LST terms ALIST)`. | — |
| `(h1-book-rewrite-equal-constraint proof index expression)` | The indexed evaluator constraint Step instantiated with the arguments of `expression` in order. | A failure from finding and instantiating the constraint. |
| `(h1-book-rewrite-equal-on-cons proof term)` | The `consp-cons` Step instantiated with the arguments of `term`. | A failure from proof construction. |
| `(h1-book-rewrite-equal-projections proof equation term)` | The Step `equation` with the constructor projections for `term` rewritten in `CAR`, then `CDR` order. | A failure from proof construction. |
| `(h1-book-rewrite-equal-refuted-quote proof test)` | A Step for the negated quote test with the equality reversed. | A failure from proof construction. |
| `(h1-book-rewrite-equal-requote proof term cons unquoted)` | A Step opening evaluation of the nonquoted application `term`, given its `CONSP` Step and the Step refuting a quoted head. | A failure from proof construction. |
| `(h1-book-rewrite-equal-substitution-invariant proof)` | The induction Step carrying expression and list evaluation through substitution. | A failure from proof construction. |
| `(h1-book-rewrite-equal-install-eval-substitution proof)` | The Prover with the evaluation invariant and flagged substitution formula installed. | A failure from proof construction. |

The constant names begin with `*h1-book-rewrite-equal-`. The suffixes
`substitute*`, `eval*`, `eval-list*`, `kwote-list*`, `environment*`, `flag*`
and `synp*` give the ACL2 symbols `MY-SUBST-EXPR1`, `EQEV`, `EQEV-LST`,
`KWOTE-LST`, `ALIST`, `FLG` and `SYNP` in prover form. The suffixes
`atom*` and `endp*` give the Common Lisp symbols `ATOM` and `ENDP`.
The suffix `quoted*` gives quoted `COMMON-LISP::QUOTE`.

`(h1-book-rewrite-equal-substitution-invariant-child selector cons-step projection proof formula same)`
uses the selector's induction hypothesis in `formula` to prove the
projected claim from the Step `same`. The integer `projection` indexes
the two conjuncts. `(h1-book-rewrite-equal-substitution-invariant-restore step expansion proof)`
reverses the selected expansion in the Step `step`. Both return a
Step or a failure.
