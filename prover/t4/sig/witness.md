# Witnesses

`proof` is a Proof as described in `prover/sig/proof.md`. Pass the Proof
component when the caller holds a Library. A comparison is a record of the
form `(:comparison witness parameters argument counterexample definition-name
necessity-name application)`. A choice rule is a record of the form
`(:choicerule name parameters argument counterexample necessity-name
definition-name)`. Names are prover symbols. Parameters are lists in formal
parameter order. `argument` is the bound variable, `counterexample` is its
predicate, and `application` is the predicate application in the comparison's
defining formula. A choice rule from `choose` has `nil` for `definition-name`.

Bindings are dictionaries, represented by insertion-ordered alists with
entries `(variable . term)`. The `choices` argument lists choice rules in
admission order. A selector result is `(argument necessity-step)` or `nil`
if no selector is found. Proof text is a string with its line endings.

A call that returns both a value and an updated Proof returns `(cons value
new-proof)`, even when its value is `nil`. Any failure is the entire result.

| Call | Result | Failure |
|---|---|---|
| `(t4-witness-comparison-read data)` | The comparison recognized in constraint data, or `nil`. | A failure for malformed fields encountered while reading. |
| `(t4-witness-choice-rule-counterexample-proof rule proof bindings)` | The Step instantiating the rule's necessity formula. | A failure from reading or constructing the Step. |
| `(t4-witness-available-choice proof kind data)` | A pair of the choice rule or `nil` and the Proof. A qualifying `choose` adds its implication fact. `kind` is a statement word and `data` is its ordered argument list. | A failure from reading the arguments or forming the fact. |
| `(t4-witness-variable-free-in variable term)` | Whether `variable` occurs free in `term`. | A failure on an empty compound encountered while descending. |
| `(t4-witness-match-counterexample pattern term rule comparison bindings)` | `(cons matched-p new-bindings)`, with parameter bindings added in traversal order. | A failure from inspecting or matching a term. |
| `(t4-witness-normal-form proof term)` | The value from simplifying `term` with `RETURN-LAST`. | A failure from simplifying the term or reading the equality. |
| `(t4-witness-witness-entry proof comparison chosen-argument necessary)` | A pair of `(step-count source)` and the Proof after removing the two helper definitions and their facts. `necessary` is the necessity Step. | A failure from constructing the entry. |
| `(t4-witness-obvious-choice proof comparison)` | Selector result for the argument-independent or constant cases. | A failure from constructing the result. |
| `(t4-witness-selector proof comparison choices)` | The first matching choice rule's selector result, or the result of trying the obvious choices. | A failure from constructing the result. |
| `(t4-witness-argument-shape proof argument guard)` | A Step fixing `argument` by the equalities and cons tests in the guard Step, or `nil`. | A failure from constructing the Step. |
| `(t4-witness-forced-argument proof comparison)` | Selector result when a guard fixes the argument. | A failure from constructing the result. |
| `(t4-witness-branch-selectors proof comparison choices)` | Selector result obtained by solving both branches of an argument-independent test. | A failure from constructing the result. |
| `(t4-witness-prove-witness proof data choices)` | A pair of `(step-count source)` or `nil` and the Proof. `data` is constraint data. | A failure from reading the comparison or constructing the entry. |
