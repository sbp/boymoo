# Evaluator witnesses

Terms, Steps, Proofs and Libraries use the forms in `prover/sig/proof.md`
and `prover/sig/library.md`. A `rule` is `(guard equality)` and an `operator`
entry is `(quoted-tag expression)`. The rules and operator entries are in
constraint order. The arguments `prefix`, `name`, `data` and `suffix` to
the witness function are a Proof, the name symbol of the constraint, its
parsed `(functions formulas)` fields, and a name suffix string.

An Evaluator is `(:evaluator lib ev list common operators obj env lst
consp operator tail suffix properties)`. `ev` and `list` are evaluator
function symbols. `common` and `operators` are the eight common rules and
the remaining operator entries, respectively. `obj`, `env` and `lst` are
formal symbols, and `consp`, `operator` and `tail` are their derived test
and selector terms. `properties` is the insertion-ordered association
list from selector symbols to lemma name symbols. `t4-evaluator-evaluator-init`
constructs the object. The accessors are `t4-evaluator-evaluator-lib`,
`t4-evaluator-evaluator-ev`, `t4-evaluator-evaluator-list`,
`t4-evaluator-evaluator-common`, `t4-evaluator-evaluator-operators`,
`t4-evaluator-evaluator-obj`, `t4-evaluator-evaluator-env`,
`t4-evaluator-evaluator-lst`, `t4-evaluator-evaluator-consp`,
`t4-evaluator-evaluator-operator`, `t4-evaluator-evaluator-tail`,
`t4-evaluator-evaluator-suffix` and `t4-evaluator-evaluator-properties`.
Each accessor takes an Evaluator and returns the named field without a
failure.

Each call in the table can return a failure in place of its result. In
method calls, `self` is the Evaluator. A result written `(cons value self)`
includes the updated Evaluator.

| ACL2 call | Result |
|---|---|
| `(t4-evaluator-replace-terms term replacements)` | The term with replacements from an association list mapping terms to terms. |
| `(t4-evaluator-argument-value term evaluator obj env values)` | The term with calls of the evaluator symbol `evaluator` replaced by selections from `values`, using the formals `obj` and `env`. |
| `(t4-evaluator-evaluator-init prefix functions common operators suffix)` | An Evaluator with the two function symbols in `functions`, common rules, operator entries and suffix. |
| `(t4-evaluator-evaluator-definitions self)` | The two definitions, each `(name formals body)`, in evaluator then list-evaluator order. |
| `(t4-evaluator-evaluator-pick self equation test)` | A Step for the branch selected in an equality Step by a test Step. |
| `(t4-evaluator-evaluator-type-of-pair self pair)` | A Step proving `CONSP` of the `CONS` term `pair`. |
| `(t4-evaluator-evaluator-list-case self args env shape)` | A Step for the list-evaluator call on `args` and `env` using the test Step `shape`. |
| `(t4-evaluator-evaluator-evaluation self term env shape tag)` | A Step for the evaluator call on `term` and `env` using the test Steps `shape` and `tag`. |
| `(t4-evaluator-evaluator-selection self proof value)` | The Step after projecting the `CONS` term `value` in `proof`. |
| `(t4-evaluator-evaluator-selector-lemma self selector)` | The Evaluator with the selector lemma and its property installed. |
| `(t4-evaluator-evaluator-select-arguments self proof)` | `(cons step self)` with the Step after promoting operand projections into evaluator calls. |
| `(t4-evaluator-evaluator-evaluates-quote self value)` | A Step proving evaluation of `KWOTE` on `value`. |
| `(t4-evaluator-evaluator-quoted-arguments self)` | `(cons name self)` with the lemma name symbol and the lemma installed. |
| `(t4-evaluator-evaluator-different-tag self test known)` | A Step rejecting `test` from the Step `known`. |
| `(t4-evaluator-evaluator-disjoint-symbol self term symbol)` | A Step rejecting `CONSP` when the Step `symbol` establishes `SYMBOLP`. |
| `(t4-evaluator-evaluator-dispatch self selected shape tag)` | `(cons step self)` with the dispatched branch. `tag` is a Step or `nil` for the lambda branch. |
| `(t4-evaluator-evaluator-rebuilt-term self goal shape not-quoted)` | `(cons step self)` with the Step for the equality `goal`, given its shape and nonquotation Steps. |
| `(t4-evaluator-evaluator-clauses self)` | `(cons steps self)` with the complete list of witness Steps in constraint order. |
| `(t4-evaluator-evaluator-witness api prefix name data suffix)` | `(count source)` for a witness, `nil` when the tactic does not apply or catches a proof failure, or a request for the definition's termination proof. |

For the witness function, initially pass `nil` for `api`. If the result
is `(:call :generate prefix "define" definition-data nil nil)`, call the
definition generator with the five fields after `:generate`. Use its
result `(count source)` or failure as `api` in a second call with the same
remaining arguments. `t4-evaluator-request-p` recognizes the request.

For `t4-slice-generate`, take the value field of its successful pair as
the generation reply. If the witness returns `(:call :used-prelude
entries target)`, call `t4-slice-used-prelude` with those arguments and
call the witness again with `(:replies generation-reply prelude-reply)`
as `api`. A prelude reply is a list `(count source)` or a failure.

`t4-evaluator-evaluator-select-arguments-selectors` takes a term and the
list evaluator symbol. It returns the first selector application in depth-first order,
`nil` if none applies, or a failure encountered during the search. `select-arguments` resumes with the rewritten proof.

The term constants are `*t4-evaluator-atom*`, `*t4-evaluator-endp*`,
`*t4-evaluator-lambda*`, `*t4-evaluator-symbolp*`, `*t4-evaluator-kwote*`,
`*t4-evaluator-kwote-list*`, `*t4-evaluator-operator*`, and
`*t4-evaluator-values*`.
