# Constraint witnesses

`lib` is a Library as specified in the shared Library signature. Terms,
symbols and Steps use the shared Proof signature. A definition option is
`(formals body)`, where `formals` is a list of variable terms. The
constant `*h3-book-witness-iff*` is the prover symbol for `IFF`.

`fields` contains a list of `(function arity)` entries followed by a
list of `(name formula)` entries. `constrained` is a set of function
symbols as a list without repeats. `names` is an insertion-ordered
alist with `(original . replacement)` entries. `mentions` observes
only membership in its set of function names. `variables` gives a
set of distinct variable terms.

The `prove` argument is a list of callback replies in invocation order.
Each is `(cons value lib)`, where `value` is a Step or failure and `lib`
is the Library after the callback. On reaching an invocation without a
reply the function returns `(:request instance witnesses)` in the
result position, paired with the Library at the invocation. Supply that
instantiated formula and the ordered list of witness symbols to the
callback, append its reply and repeat the original call. The result
preserves the Library on success, a request or a failure.

| ACL2 call | Result |
|---|---|
| `(h3-book-witness-replace-functions term names)` | The term with renamed function heads, or a failure. |
| `(h3-book-witness-mentions term names)` | Whether a term uses a function in the given set of names, or a failure. |
| `(h3-book-witness-variables term)` | The set of variable terms, or a failure. |
| `(h3-book-witness-define lib formals body)` | `(cons value lib)` with the witness symbol or a failure as `value`. |
| `(h3-book-witness-equations-for function arity formulas constrained)` | The list of inferred definition options in trial order, or a failure. |

A variable set is ordered lexically by each element's written ACL2
representation. Equation options precede recognizer options. Witness
choices follow Cartesian product order.

The witness call can prepare its ordered candidates once for a sequence
of callback requests.

| ACL2 call | Result |
|---|---|
| `(h3-book-witness-prepare lib fields)` | `(cons value lib)`, where `value` is `(function-names formulas candidates)` or a failure. The Library contains the definitions for the candidates. `function-names` is a list of symbols in declaration order. `candidates` contains up to 28 witness symbol lists in trial order. |
| `(h3-book-witness-try-options lib function-names formulas candidates prove)` | The entry, callback request or failure paired with the updated Library. Use the Library and three fields from the preparation result and the same ordered callback replies as in `witness-proof`. |
