# Bounded tail recursion

`proof` is the H2 proof context. Terms and Steps use the forms in
`prover/sig/proof.md`. A result described as `(cons value proof)` includes
the resulting proof context, with any added lemmas and changed search rules.
A failure from proof construction is the entire result, where applicable.

| Function and arguments | Result |
|---|---|
| `(h2-tail-recursion-reached state bound)` | The term for reaching a stopping state after iterating from term `state` with term `bound`. No failure. |
| `(h2-tail-recursion-positive-bound proof reach testing)` | The Step proving a positive bound, from the Step `reach` proving reachability and the Step `testing` for the false stopping test of the initial state. May return a failure. |
| `(h2-tail-recursion-evaluation-branch proof state bound index testing)` | The equation Step for the bounded evaluation branch selected by index Step `index` and stopping-test Step `testing`, for terms `state` and `bound`. May return a failure. |
| `(h2-tail-recursion-stops-early proof state bound testing)` | The equation Step for bounded evaluation at an already stopping state, using Step `testing` and terms `state` and `bound`. May return a failure. |
| `(h2-tail-recursion-synchronized-evaluation proof)` | `(cons name proof)` with the symbol of the lemma equating two bounded evaluations that reach a stop. May return a failure. |
| `(h2-tail-recursion-choose-bound proof reached-end)` | The Step showing that the chosen bound reaches a stop, given the Step `reached-end` for another bound. May return a failure. |
| `(h2-tail-recursion-prepend-transition proof state reached-end)` | `(cons step proof)` with the Step proving reachability from term `state` by extending the bound in Step `reached-end`. May return a failure. |
| `(h2-tail-recursion-tail-recursive-equation proof formula)` | `(cons step proof)` with the Step proving the tail-recursive equation term `formula`. May return a failure. |

The proof context is the inherited Recipes object described in
`prover/h2/sig/recipes.md`. The calls that derive Steps can return a Search
method request as their entire result. A successful search leaves the
unconsumed replies in the returned Recipes.
