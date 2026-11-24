# Theorem and witness recipes

`lib` is the B2 Tactics library. Terms and Steps are as specified in
`prover/sig/proof.md`. A constrained function is `(name arity)`, and a
constraint formula is `(name formula)`. Both lists keep input order. The
functions can return a failure in place of the stated result. `prove-theorem`
returns an `Unproved` failure when no recipe applies.

| Function | Arguments in order | Result |
|---|---|---|
| `b2-recipes-legal-variable` | `lib`, formula term | Step proving the implication from a legal variable to a symbol |
| `b2-recipes-distributivity` | `lib`, formula term | Step proving distribution of a right-hand multiplicative factor |
| `b2-recipes-oracle-state` | `lib`, formula term | Step proving preservation of the state predicate |
| `b2-recipes-prove-theorem` | `lib`, theorem name, formula term | `(cons step lib)` with the proof and the library including any auxiliary lemmas |
| `b2-recipes-prove-witness` | `lib`, list of constrained functions, list of constraint formulas | `(cons entry lib)` with the witness entry in the form returned by `proof-proof-entry` and the library including the witness definitions |
