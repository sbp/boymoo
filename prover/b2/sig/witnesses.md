# Constraint witnesses

`lib` is a B2 tactics library. `functions` is the ordered list of
`(name arity)` declarations. `formulas` is the ordered list of
`(name formula)` constraints. Names and terms follow `prover/sig/proof.md`.

`*b2-witnesses-synp*` is the symbol for `SYNP` in package `ACL2`.

| Call | Result | Failure |
|---|---|---|
| `(b2-witnesses-interpretation name index formulas)` | `(formals body)` for constraint function `name` at zero-based index `index`. `:none` in the formals field asks for default `ARG-i` formals. | Failure from reading malformed data. |
| `(b2-witnesses-find-witnesses lib functions formulas)` | `(cons entry lib)` with the witness proof entry and the library extended with the witness definitions in declaration order. The entry follows `proof-proof-entry`. | `unproved` for an arity mismatch or failed proof, or a failure from defining or proving the witnesses. |
