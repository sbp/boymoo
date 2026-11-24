# Constraint witnesses

The argument `proof` is the H1 Prover described in
`prover/h1/sig/tactics.md`. Terms, Steps and entries use the forms in
`prover/sig/proof.md`. The string `raw` contains the constraint statement
bytes exactly as supplied for hashing. Constraint `fields` is
`(functions formulas)`. The functions are ordered `(name arity)` pairs.
The formulas are ordered `(name formula)` pairs.

| Call | Result | Failure |
|---|---|---|
| `(h1-book-witness-witness-entry proof raw fields)` | `(cons entry proof)` with the witness entry and the Prover after its auxiliary definitions and lemmas. | `Unproved` for unsupported constraints, or a failure from reading terms or constructing proofs. The failure is the entire result. |
| `(h1-book-witness-evaluator-equations functions formulas)` | Alist from evaluator names to the same list of `(formula-name operation)` pairs. Each equation list is in formula order. The evaluator names are in canonical symbol order and a missing operation is `nil`. Returns `nil` when the constraints do not describe a pair of binary evaluators. | A failure from reading terms or checking selector paths. |
| `(h1-book-witness-evaluator-proof proof formula evaluators)` | Step proving `formula`. The caller supplies its `evaluators` alist as given by `evaluator-equations`, extended by the declarations in scope. | `Unproved` for absent equations or a failed search, or a failure from constructing proofs. |

`rename-calls` receives a term and an alist from old to new function
heads. It preserves the order of actual arguments and recurses into
lambda bodies. `projection` takes a formula and constrained name and
returns `(slot position)`; the direct result has slot `:none`. Both
positions and numeric slots start at zero. `projection-witness` has
the arguments and returns the pair specified for `witness-entry`.

A Dispatch is `(:h1-dispatch proof prefix branches definitions encoder
features root)`. Its input operations map operation symbols to result
terms in registration order. `branches` maps each internal dispatch
symbol to `(split equations)` in definition completion order. Its two
equation names are for the true and false branches, in that order.
`definitions` is the count of allocated definitions. `encoder` is the
optional encoding function symbol, `features` is the list of
`(component offset)` pairs in selection order, and `root` is the root
dispatch function symbol. `dispatch-keys` returns `(features keys)`,
where the `keys` alist follows operation registration order.

An EvaluatorWitness is `(:h1-evaluator-witness proof prefix value values
name cases positions dispatch)`. Its `value` and `values` are the
generated function symbols, `name` is the first constrained function,
and `cases` is the list of `(obligation bindings canonical operation)`
in formula order. The bindings alist pairs (X) and (Y) with the
actual parameters in that order. `positions` is a list of distinct
positions in ascending numerical order. Its Dispatch carries the
Prover as of dispatch construction. Evaluating a case uses the current
Prover of the EvaluatorWitness. Updating methods return the resulting
object or pair their value with that object, and failures are entire
results.
