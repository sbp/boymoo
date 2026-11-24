# Evaluator witnesses

The terms and Steps have the forms described in `prover/sig/proof.md`. A Library
has the form described in `prover/sig/library.md`. `functions` passed to the
constructor is the ordered list of constrained function symbols. `constraints`
is the ordered list of `(name formula)` pairs. The function table is a list of
`(operator body)` pairs from the constraints, in their input order.

An Evaluator is `(:b1-evaluator lib tag engine term-fn list-fn functions table)`.
Its fields are available through `b1-evaluators-evaluator-lib`,
`b1-evaluators-evaluator-tag`, `b1-evaluators-evaluator-engine`,
`b1-evaluators-evaluator-term-fn`, `b1-evaluators-evaluator-list-fn`,
`b1-evaluators-evaluator-functions`, and `b1-evaluators-evaluator-table`.
These accessors take an Evaluator and return the field without a failure.
`(b1-evaluators-evaluator-with-lib evaluator lib)` replaces its Library.
The `functions` field lists the term function followed by the list function.
The constant `*b1-evaluators-a*` is the default environment term.
The constant `*b1-evaluators-quote-name*` is the quoted `QUOTE` symbol.

| Call | Result | Failure |
|---|---|---|
| `(b1-evaluators-after-cdrs term count)` | Term with `count` applications of `CDR` around it. | A failure for an invalid count. |
| `(b1-evaluators-argument term index)` | Term for the `CAR` after `index` applications of `CDR`. | The same as `after-cdrs`. |
| `(b1-evaluators-evaluator-init lib functions constraints)` | Evaluator with the Library extended by the new definitions. | A failure from reading the constraints or constructing the definitions. |
| `(b1-evaluators-evaluator-evaluate evaluator term environment)` | Evaluator engine call with false list mode. | None. |
| `(b1-evaluators-evaluator-evaluate-list evaluator terms environment)` | Evaluator engine call with true list mode. | None. |
| `(b1-evaluators-evaluator-install evaluator constrained-term)` | Evaluator with the engine and its two wrappers installed in its Library. | A failure from term traversal, measure proofs or entry construction. |
| `(b1-evaluators-evaluator-open evaluator call evidence rules wrappers)` | Normalized equality Step for `call`. | A failure from normalization. |
| `(b1-evaluators-evaluator-selector-law evaluator index terms environment)` | `(cons step evaluator)` with a Step for the selector law instantiated at `terms` and `environment`, and the resulting Evaluator. | A failure from proof construction. |
| `(b1-evaluators-evaluator-quote-arguments evaluator)` | `(cons rule evaluator)` with the rewrite rule for the evaluated argument list and the resulting Evaluator. | A failure from proof or rule construction. |
| `(b1-evaluators-evaluator-constraint evaluator number formula)` | `(cons step evaluator)` with the constraint Step for `formula` at its zero-based `number`, and the resulting Evaluator. | A failure from proof construction. |

Pass `*b1-evaluators-a*` for an omitted environment in `evaluate` and
`evaluate-list`. The bound in `b1-evaluators-after-cdrs` or
`b1-evaluators-argument` is an integer. The Boolean bounds `t` and `nil`
act as one and zero.
Omitted `evidence`, `rules`, and `wrappers` are `nil`. Evidence lists contain
Steps, wrapper lists contain function symbols, and rule lists use the rules
of `prover/b1/sig/logic.md`, in application order. A failure is the entire result.

The other term constants are `*b1-evaluators-mode*`, `*b1-evaluators-kwote*`,
`*b1-evaluators-kwote-list*`, `*b1-evaluators-pairlis*`, and
`*b1-evaluators-assoc*`.
