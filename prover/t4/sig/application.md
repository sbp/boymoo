# Application measures

Terms, Steps, the Library, and Calls have the forms in
`prover/sig/proof.md`, `prover/sig/library.md`, and `prover/sig/termination.md`.
Evidence is the structural Evidence object. Each function can return a
failure in place of a listed value.

The constants `*t4-application-apply*`, `*t4-application-apply-lambda*`,
`*t4-application-ev*`, `*t4-application-primitive*`,
`*t4-application-tame-function*`, and `*t4-application-badge*` are the
ACL2 symbols `APPLY$`, `APPLY$-LAMBDA`, `EV$`, `APPLY$-PRIMP`,
`TAMEP-FUNCTIONP`, and `BADGE`. The constant
`*t4-application-specials*` is the list of the `APPLY$` and `EV$`
symbols in that order.

| ACL2 call | Result |
|---|---|
| `(t4-application-measures definitions)` | An alist from defined function names to measure terms. The definition triples contain two formals each. The result follows the order of first insertion, with a repeated name's measure replaced in place. |
| `(t4-application-close-tame-branch lib obj evidence goal)` | `(cons (list step evidence) lib)`, with the proof or `nil` and the resulting Evidence and Library. The object and goal are terms. |
| `(t4-application-descent-compare left right evidence lib call)` | `(cons step lib)`, with the proof comparing the selected measure terms and the resulting Library. |
| `(t4-application-descent lib goal call)` | `(cons step lib)`, with the proof of the ordinal comparison term and the resulting Library. |
