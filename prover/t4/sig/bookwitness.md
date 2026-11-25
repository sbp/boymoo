# Book witnesses

Terms, prover symbols and Steps use the forms in `prover/sig/proof.md`.
The proof context uses the Library form in
`prover/sig/library.md`. Constraint data is `(functions formulas)`.
Each function is `(name arity)` and each formula is `(name term)`.
The order of both lists is their order in the constraint.

| Call | Result | Failure |
|---|---|---|
| `(t4-bookwitness-replace-functions term names)` | The term with function names replaced, including inside lambda bodies. `names` is an association list of `(old-name . new-name)` entries. Quoted data is left alone. | A failure from inspecting a malformed term. |
| `(t4-bookwitness-simple-witness api tactic name data suffix)` | `(cons value lib)`, where `value` is `(step-count source)`, `nil` when there is no witness, or a request described below. `tactic` is its Library, `name` is the constraint name, and `suffix` is the string used in auxiliary names. | A failure from reading arguments, constructing a proof, or a supplied reply. See `prover/t4/notes/failures.md` for failures that let the search try another candidate. |

`api` is the ordered list of replies to the requests in this invocation.
Start with `nil`. For `(:call :solve lib goal)`, put `lib` into the
BookLogic tactic, set its remaining budget to 850, and call its solver on
`goal` with default arguments. Append `(cons step lib)`, taking the
Library from the tactic after the call and putting any failure in the Step
position. For `(:call :used-prelude entries target)`, append the result
of the prelude selection, a list `(step-count source)` or a failure.
Repeat the original call with the extended reply list. Use
`t4-bookwitness-request-p` to recognize a request.

Before the first call for a search, the caller sets the tactic's enabled
set to `nil` and its total remaining budget to `:none`. The caller
keeps other tactic fields as the solver leaves them. Use the Library in
the final pair for the tactic's proof data after auxiliary function
cleanup. The source string includes the proof entry and its prelude with their
line endings.
