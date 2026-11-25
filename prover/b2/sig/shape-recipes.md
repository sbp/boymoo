# Shape recipes

The Library, terms and Steps have the forms in `prover/sig/library.md`
and `prover/sig/proof.md`.

| Call | Result | Failure |
|---|---|---|
| `(b2-shape-recipes-patterns)` | The list of `(schematic recipe . arguments)` entries in recipe trial order. `recipe` is a keyword identifying the proof recipe and `arguments` is its list of fixed arguments after the Library. | — |
| `(b2-shape-recipes-prove-shape library formula)` | `(cons step library)` with the Step instantiated for `formula` by the first matching recipe and the resulting Library. | `unproved` when no schematic matches, or a failure from matching or proof construction. |

`*b2-shape-recipes-routes*` is an ordered association list keyed by
schematic head. The keys are in first-occurrence order. The value at each
key is the list of its pattern entries in traversal order.
