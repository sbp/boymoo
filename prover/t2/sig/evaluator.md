# Evaluator witnesses

`lib` is a Library, `generator` is the Generator from the `tactics`
signature, and `context` is its RulerFacts object. Terms and Steps use
the shared representations. The function names are `*t2-evaluator-eval*`,
`*t2-evaluator-eval-list*` and `*t2-evaluator-apply*`. The other constants
are `*t2-evaluator-operator-constraints*`, `*t2-evaluator-symbolp*`,
`*t2-evaluator-endp*`, `*t2-evaluator-atom*`, `*t2-evaluator-kwote*`,
`*t2-evaluator-kwote-list*`, `*t2-evaluator-assoc*` and `*t2-evaluator-pairlis*`.

Any failure is the entire result. Dispatch entries are `(operator arity)`
lists in constraint order. A witness map is an association list from each
abstract function name to its concrete function name, in declaration order.
An optional environment uses `:none` for omission.

| Function | Arguments and result | Failure |
|---|---|---|
| `(t2-evaluator-car term)` | The `CAR` application to `term`. | None. |
| `(t2-evaluator-cdr term)` | The `CDR` application to `term`. | None. |
| `(t2-evaluator-nth index term)` | The term for taking `CAR` after `index` applications of `CDR`. | None for an integer index. |
| `(t2-evaluator-rename term witnesses)` | `term` with application heads renamed from the witness map, including lambda bodies and excluding quotations and lambda formals. | A failure from a malformed compound. |
| `(t2-evaluator-operators formulas)` | The dispatch entries read from the list of operator equations. | A failure from a malformed equation or an unmet precondition. |
| `(t2-evaluator-install generator dispatch)` | The Generator with the evaluator definitions installed and their proof entry appended to its Library. | A failure from constructing the definitions or their measure proof. |
| `(t2-evaluator-select lib equation evidence)` | The equation Step after selecting successive branches with the evidence Steps, in order. | A failure from proof construction. |
| `(t2-evaluator-cons-truth lib first rest)` | The Step that the constructed pair is a cons. | A failure from proof construction. |
| `(t2-evaluator-cons-selectors lib first rest)` | The list of `CAR-CONS` and `CDR-CONS` Steps. | A failure from proof construction. |
| `(t2-evaluator-false-test lib equation)` | The Step negating the left side of an equality Step to quoted `NIL`. | A failure from proof construction or an unmet precondition. |
| `(t2-evaluator-end-test lib term)` | The Step unfolding the end-of-list test and its resulting call. | A failure from proof construction. |
| `(t2-evaluator-open-cons lib function first rest environment)` | The Step unfolding the application on a constructed pair, with an environment when supplied. | A failure from proof construction. |
| `(t2-evaluator-eval-nil lib environment)` | The Step evaluating the quoted `NIL` term in the given environment. | A failure from proof construction. |
| `(t2-evaluator-list-projections lib)` | Library with the two evaluator list projection lemmas added in selector order. | A failure from proof construction or an unmet precondition. |
| `(t2-evaluator-quoted-value lib value)` | The Step evaluating the quotation produced for `value`. | A failure from proof construction or an unmet precondition. |
| `(t2-evaluator-quoted-arguments lib)` | Library with the quoted-arguments lemma added. | A failure from proof construction. |
| `(t2-evaluator-known-path n lib equation context)` | Pair `(cons step context)` with the equation Step after selecting known branches and the resulting RulerFacts. Pass `1000000` as the initial fuel. | A failure from proof construction or `Fuel`. |
| `(t2-evaluator-arguments lib dispatch base environment arity)` | The dispatch equation Step with its result arguments replaced by evaluation at the corresponding source positions. | A failure from proof construction. |
| `(t2-evaluator-constraint lib formula index)` | The Step proving `formula` at its zero-based constraint position `index`. | A failure from proof construction or an unmet precondition. |
| `(t2-evaluator-witness generator data)` | `(cons entry generator)` where `entry` is the witness proof entry for the parsed `constrain` data, and the Generator contains the extended Library. | `Unproved` for an inapplicable witness shape, or a failure from reading the constraints or proof construction. |
