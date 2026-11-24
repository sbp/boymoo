# Names for a recursion group

Terms and symbols have the forms in `prover/sig/proof.md`. A definition is
`(name formals body)`. A name map is an association list with entries
`(original . replacement)` in order of first declaration.

| Function | Arguments and result |
|---|---|
| `(t2-rename-rename-calls term names)` | Term and name map. Returns the term with its call operators renamed. |
| `(t2-rename-fresh-definition rulers definitions)` | Ruler extenders and list of definitions. Returns `(rulers definitions names)` with the renamed extenders and definitions in their supplied order, and the name map. |

Both functions can return a failure for malformed term or definition data.
