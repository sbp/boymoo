# Recursive warrant proofs

`proof` is a Proof, `step` is a Step, and terms and bindings have the forms in `prover/sig/proof.md`. `comparison` is a Comparison and `selector` is a ChoiceRule from `witness.lisp`. `tests` is a list of `(term holds)` pairs in the order in which branches were entered. `holds` is `t` for the true branch and `nil` for the false branch.

| Function | Arguments and result | Failure |
|---|---|---|
| `(l1-recursive-has-lambda term)` | Whether evaluation of the term encounters a lambda application. | Malformed term. |
| `(l1-recursive-primitive-helpers proof body recursive)` | Names of the helpers called by `body`, excluding `recursive`, whose definitions call only primitives or `IF`. Names are ordered by package and symbol name. | A failure from the table lookup or the traversal of a term. |
| `(l1-recursive-introduce-implication proof hypothesis result)` | A Step introducing `hypothesis` as the antecedent of the implication with `result` as its consequent. | A failure from proof construction. |
| `(l1-recursive-list-wrapper proof function formals body)` | A Step opening the list-valued wrapper of `function`, whose definition has the given formals and body. | `unsupported-application` for an unsupported wrapper or a failure from proof construction. |
| `(l1-recursive-scalar-wrapper proof function formals body)` | A Step opening a wrapper that returns a scalar on a singleton. | `unsupported-application` for an unsupported wrapper or a failure from proof construction. |
| `(l1-recursive-list-wrapper-wrapper argument cons proof function)` | The wrapper equation under the given Boolean `cons` assumption. | A failure from proof construction. |
| `(l1-recursive-scalar-wrapper-open-at f arg tests proof other)` | The equation opening `f` at `arg` and `other` under the signed tests. | A failure from proof construction. |
| `(l1-recursive-scalar-wrapper-cons-result arg proof name other)` | The equation giving the helper's list construction at `arg` and `other`. | `unsupported-application` for an unsupported helper or a failure from proof construction. |
| `(l1-recursive-scalar-wrapper-head-of step cons proof)` | The wrapper equation after substituting the list construction `cons` and projecting its head. | A failure from proof construction. |
| `(l1-recursive-recurrence-init proof comparison badge-test)` | A Recurrence for the comparison under the badge test. | `unsupported-application` for unsupported recursive calls or wrappers, or a failure from term or proof construction. |
| `(l1-recursive-recurrence-at recurrence term argument)` | `term` with the recurrence's argument variable replaced by `argument`. | A failure from substitution. |
| `(l1-recursive-recurrence-child-agreement recurrence tests)` | A Step proving agreement on the recursive argument under the given branch tests. | `unsupported-application` for a missing cons test or a failure from proof construction. |
| `(l1-recursive-recurrence-local-agreement recurrence logical oracle tests)` | A Step establishing that a single unfolding agrees with the logical value when its child agrees. Pass `nil` for an omitted `logical` or `oracle` equality Step. | A failure from proof construction or `fuel`. |
| `(l1-recursive-recurrence-comparison-equation recurrence)` | `(left right step)` giving the two quoted designators and their comparison equation. | A failure from application or proof construction. |
| `(l1-recursive-recurrence-when-child-agrees recurrence condition agreement)` | A Step proving `condition` using the `agreement` Step on its true branch. | A failure from proof construction. |
| `(l1-recursive-recurrence-induct recurrence left right selector picked)` | `(premise step)` giving the selected premise and the universal agreement Step. | A failure from proof construction. |
| `(l1-recursive-recurrence-locate recurrence picked premise bad-argument bad-failure)` | `(chosen step)` giving the selected argument and the implication Step for its failure. `bad-argument` is the argument and `bad-failure` is its failure Step when the badge fails. | A failure from proof construction. |

The constants are `*l1-recursive-user-application*`, `*l1-recursive-local-agreement*`, `*l1-recursive-step-comparison*`, `*l1-recursive-universal-agreement*`, `*l1-recursive-control*` and `*l1-recursive-atom*`.
