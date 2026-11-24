# Witness candidates

`lib` is a Library as specified in `prover/sig/library.md`. `search` is a
theorem search as specified in `prover/t3/sig/book-theorems.md`. Terms and
Steps have the forms in `prover/sig/proof.md`. A declaration is
`(function arity)` and a named formula is `(name formula)`. Their lists
retain the given order. A candidate is `(formals body)` with an ordered
list of formal variable terms and a body term. A proof entry has the form
returned by `proof-proof-entry`.

| Call | Result | Failure |
|---|---|---|
| `(t3-book-witnesses-candidate-bodies lib function arity formulas declared)` | The candidate definitions in generation order, including repeated candidates. `function` is the symbol being defined, `arity` its integer arity, `formulas` the named constraints, and `declared` the list of symbols being witnessed. | A failure from reading a constraint or invalid arity. |
| `(t3-book-witnesses-witness-proof lib search declarations formulas)` | `(list entry lib search)` for the first successful witness and the resulting Library and theorem search states. Equal candidates are tried once per function. The rightmost candidate list varies fastest. | `Unsupported` when no candidate works, or a construction or search failure. |

`*t3-book-witnesses-iff*` is the `IFF` symbol. Failures are the entire result.
Arity accepts the Boolean bounds in
`prover/t3/sig/book-evaluators.md`.
