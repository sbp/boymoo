# Witness proofs

A Proof, Step and term have the forms in `prover/sig/proof.md`. A constraint
is the two-element list `(functions formulas)`. The elements of
`functions` are `(name arity)` and those of `formulas` are `(name term)`,
both in statement order.

The record forms are `(:comparison witness parameters argument
counterexample definition-name necessity-name application)` and
`(:choicerule name parameters argument counterexample necessity-name
definition-name)`. Parameters are terms in the order of the predicate's
formals. The final field of a ChoiceRule is `nil` when there is no
definition fact.

`l1-witness-make-comparison` and `l1-witness-make-choice-rule` take the
fields in the order above. The accessors are named by the record and field,
for example `(l1-witness-comparison-counterexample comparison)` and
`(l1-witness-choice-rule-parameters rule)`. The symbol constants are `*l1-witness-choice*`,
`*l1-witness-selector*` and `*l1-witness-predicate*`.

Pass `""` for the default tag and `nil` for an omitted normalization.
A witness entry is `(count source)` with the proof step count and the
complete entry text. A binding map is an insertion-ordered association
list of `(variable . term)` pairs.

| ACL2 call | Arguments and result | Failure |
|---|---|---|
| `(l1-witness-comparison-read data)` | Constraint data. Returns a Comparison or `nil` for an unrecognized comparison. | A failure from reading malformed constraint data. |
| `(l1-witness-choice-rule-counterexample-proof rule proof bindings)` | A ChoiceRule, a Proof and an insertion-ordered binding map. Returns the instantiated counterexample Step. | A failure from proof construction. |
| `(l1-witness-admit proof kind data)` | A Proof, a statement kind string and its data. Returns `(cons choice proof)` with the resulting Proof and a ChoiceRule or `nil`. | A failure from reading the statement or admitting it. |
| `(l1-witness-available-choice proof kind data)` | The same arguments and pair result as `admit`. Registers the axiom of a supported choice statement. | A failure from reading the statement or constructing the axiom. |
| `(l1-witness-match-counterexample pattern term rule comparison bindings)` | A pattern term, target term, ChoiceRule, Comparison and binding map. Returns `(cons matched-p bindings)` with the bindings inserted before the match stopped. | A failure from reading a malformed term. |
| `(l1-witness-normal-form proof term)` | A Proof and a term. Returns the term after the `RETURN-LAST` simplification. | A failure from proof construction. |
| `(l1-witness-predicate-necessity proof comparison expanded necessary)` | A Proof, a Comparison, and Steps for the expanded predicate and the necessity implication. Returns the necessity Step with the predicate in the conclusion. | A failure from proof construction. |
| `(l1-witness-witness-entry proof comparison chosen-argument necessary tag)` | A Proof, a Comparison, the chosen term, its necessity Step and a tag string. Returns the witness entry, or `nil` when a helper name is occupied. | A failure from proof construction or writing. |
| `(l1-witness-obvious-choice proof comparison)` | A Proof and a Comparison. Returns `(argument consequence)` for the first constant that works, or `nil`. | A failure from proof construction. |
| `(l1-witness-prove-witness proof data choices tag)` | A Proof, constraint data, a list of ChoiceRules in their admission order and a tag string. Returns a witness entry or `nil`. | A failure from reading the comparison or constructing the proof. |
| `(l1-witness-counterexample-choice proof constraint)` | A Proof and constraint data. Returns `(cons (list statement source) proof)`, where `statement` is the new choice statement text, `source` is the witness proof text and the Proof has the temporary choice fact removed. | A failure from reading the comparison, constructing the proof, or writing. |
| `(l1-witness-choice-statements proof constraint normalization)` | A Proof, constraint data and an optional normalization Step. Returns `(cons (list statements source reverse) proof)`. The first two elements are the choice, definition and theorem statements and their proof text. The last is a pair of strings for the theorem proving the converse and its proof. The Proof has the temporary definition and facts removed. | A failed normalization assertion or a failure from reading the comparison, proof construction, or writing. |
| `(l1-witness-dependencies term)` | A term. Returns distinct call heads ordered by the ACL2 text of their data, skipping quotations and following only the value of `RETURN-LAST`. | A failure from reading malformed terms. |
| `(l1-witness-affected-constraints statements before functions)` | Statement rows `(raw kind data)`, an exclusive one-based statement number, and the initial set of function names as a list. Returns all affected `(number name)` pairs in statement and formula order. | A failure from reading a malformed term or statement. |

A failure is the entire result unless specified otherwise.

`l1-witness-witness-entry-with-proof` and `l1-witness-prove-witness-with-proof`
take the arguments of the corresponding calls above and return
`(cons result proof)`. When a witness entry is constructed, the Proof
has the two temporary helper definitions and their facts removed.
`(l1-witness-admitted-fact-names kind data choice)` returns the names of the facts written by a successful `l1-witness-admit`, in write order. `choice` is the choice component of that result. The names may repeat if a line writes the same fact more than once.
