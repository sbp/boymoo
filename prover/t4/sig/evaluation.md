# Evaluator equations and folds

Terms, Steps, and the Library use the forms in `prover/sig/proof.md` and
`prover/sig/library.md`. An EvaluationRules object has the form
`(:t4-evaluation-rules calls spines reapplications functions)`. The three
maps are association lists in insertion order. Their keys are respectively
`(evaluator quoted-tag)`, `(list-evaluator consp-p)`, and
`(evaluator list-evaluator)`. Each value is `(name syntax env)` for a fact
name and its two formal variables. The functions set is a list in insertion
order and is queried by membership.

| Call | Result | Failure |
|---|---|---|
| `(t4-evaluation-evaluation-rules-init)` | An empty EvaluationRules object. | None. |
| `(t4-evaluation-make-evaluation-rules calls spines reapplications functions)` | EvaluationRules with those fields. | None. |
| `(t4-evaluation-evaluation-rules-calls rules)` | Call rule map of `rules`. | None. |
| `(t4-evaluation-evaluation-rules-spines rules)` | List spine rule map of `rules`. | None. |
| `(t4-evaluation-evaluation-rules-reapplications rules)` | Reapplication rule map of `rules`. | None. |
| `(t4-evaluation-evaluation-rules-functions rules)` | Evaluator function set of `rules`. | None. |
| `(t4-evaluation-evaluation-rules-register rules data)` | Updated EvaluationRules. `data` is `(functions formulas)`, using `(name arity)` function records and `(name formula)` formula records. | From unpacking or inspecting a record. |
| `(t4-evaluation-evaluation-rules-syntax-terms rules formula)` | Syntax input terms in generator order, with repeats preserved. | From inspecting a formula. |
| `(t4-evaluation-evaluation-rules-equation rules lib term evidence replies)` | `(cons step (cons lib evidence))` for the first evaluator equation or for a missing equation with `step` equal to `nil`. | From reading the term, a query, or a proof operation. |
| `(t4-evaluation-evaluation-rules-reapply rules lib term list-evaluator cons distinct replies)` | `(cons step lib)` for the evaluator call on its operator and evaluated arguments. `cons` is the Step for its syntax being a cons and `distinct` is the Step excluding its quote tag. | A failure for an unregistered pair, or a failure from a query or proof operation. |
| `(t4-evaluation-evaluation-fold lib formula rules replies)` | `(cons step lib)` for the fold theorem, with `step` equal to `nil` when inapplicable. | From a query or proof operation, or a failure for a missing evaluator equation, non-cons list result, unexpected fold, or missing connective law. |

The last three calls can request an operation supplied by the tactic context. A
request has the form `(:t4-evaluation-request operation arguments lib)`.
`t4-evaluation-request-p` recognizes it, and `t4-evaluation-request-operation`,
`t4-evaluation-request-arguments`, and `t4-evaluation-request-library`
return its fields. The recipe consumes `replies` left to right. Start with
`nil`, and for each request append the result of the operation to the
replies and repeat the call with its original arguments. A failure reply is
the result of the entire call.

| Operation | Arguments | Reply |
|---|---|---|
| `:known` | `(term evidence)` | `(cons step (cons lib evidence))`, with the resulting Library and Evidence and with `nil` for a missing Step. |
| `:find` | `(term evidence)` | The `:known` reply form for a direct Evidence query. |
| `:prove` | `(term evidence-steps definitions)` | `(cons step lib)` with the resulting Library. |
| `:simplify` | `(term evidence-steps definitions)` | `(cons step lib)` with the resulting Library, with `nil` when unchanged. |
| `:evaluation` | `(call tests)` | `(cons step lib)` with the Library from the evaluator equation recipe using fresh Evidence. |
| `:fact-proof` | `(term)` | `(cons step lib)` from a fact proof with fresh Evidence, with `nil` for a missing Step. |
| `:use-arithmetic` | `nil` | The resulting Library. |

The term constants are `*t4-evaluation-iff*`, `*t4-evaluation-atom*`,
`*t4-evaluation-endp*`, `*t4-evaluation-kwote-list*`, and
`*t4-evaluation-synp*`.
