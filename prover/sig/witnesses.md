# Witness proof signatures

`lib` is a library, `step` is a proof step, `term` is a prover term and `bindings` is a list of `(variable term)` pairs. Functions that construct proof steps can return a failure in place of their result.

`*witnesses-witnesses*` is an alist from ASCII function names without a package to recipe lists. A recipe is either an ASCII constant recipe name or a prover symbol for a witness function.

| ACL2 call | Arguments and result |
|---|---|
| `(witnesses-witness lib recipe arity)` | `arity` is the constrained function's number of arguments. Returns `(cons name lib)` with the witness symbol and any new definition, or a failure. |
| `(witnesses-rational-negation lib term evidence)` | `evidence` is a list of proof steps. Returns a proof that the negation of a rational is rational when applicable, or nil. |
| `(witnesses-prove-formula n lib term definitions evidence)` | `n` is fuel, `definitions` is a list of definition names and `evidence` is a list of proof steps. Returns a proof of `term` or a failure. The initial fuel is `1000000`. |
| `(witnesses-df-fact-locations term path)` | `path` is the list of indices reaching `term`. Returns all paths to constrained `TO-DF` calls in argument-first order. |
| `(witnesses-df-fact lib name bindings)` | `name` is the ASCII name of a constraint fact. Returns a proof step that expresses the fact using `TO-DF`. |
| `(witnesses-dfp-proof lib value rational fixed)` | `value` is a term, and `rational` and `fixed` prove rationality and the fixed-point equation for `value`. Returns a proof of `DFP` for `value`. |
| `(witnesses-dfp-fixed-point lib premise)` | `premise` proves a `DFP` application. Returns a proof of its fixed-point equation. |
| `(witnesses-prove-implication lib term premise consequence)` | `term` is an implication, and `premise` and `consequence` are proofs of its respective arguments. Returns the proof of the implication. |
| `(witnesses-rounding-formula lib name term)` | `name` is the ASCII name of the rounding formula `term`. Returns its proof. |
| `(witnesses-zero-dfp lib term)` | `term` is a `DFP` application whose argument unfolds to zero. Returns `(cons step lib)` with a proof of `term`. |
| `(witnesses-witness-proofs lib data)` | `data` is `(functions formulas)`. Each function is `(name arity)` and each formula is `(name term)`. Returns `(cons (list entry method) lib)` with the proof entry and method string. |
