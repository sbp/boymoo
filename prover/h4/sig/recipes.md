# Result, warrant and congruence recipes

`p` is the H4 Tactics library. Formulas are prover terms and Steps have the
form in `prover/sig/proof.md`. A failure is the entire result. A returned library
carries the facts and entries in insertion order.

| ACL2 call | Result | Failure |
|---|---|---|
| `(h4-recipes-recipe formula)` | Keyword identifying the first matching recipe, or `nil`. | Shape or indexing error on a malformed formula. |
| `(h4-recipes-recognized-result p formula)` | Step for the result recognizer. | A failure from proof construction or a missing recognizer fact. |
| `(h4-recipes-rationalize-round-trip p formula)` | Step for the round trip under the premise. | A failure from proof construction or exhausted expansion attempts. |
| `(h4-recipes-legal-name p formula)` | Step for the implication about a legal name. | A proof error. |
| `(h4-recipes-natural-measure p formula)` | `(cons step p)` with the natural measure Step and the updated library. | A failure from proof construction or an unexpected measure body. |
| `(h4-recipes-apply tactic p formula warrant-filters)` | `(cons step p)` from the selected recipe. The filter list supplies the definitions prepared for the warrant recipe. Pass `nil` for that argument for all other recipes. | A failure from the selected recipe. |

The selector returns `:recognized-result`, `:warrant-recipe`,
`:natural-measure`, `:fn-equal-is-equivalence`, `:do-congruence`,
`:loop-congruence`, `:rationalize-round-trip`, `:legal-name`,
`:term-implies-pseudo`, `:term-list-implies-pseudo` or `:arity-or-logic`.
`*h4-recipes-from-df*` is the symbol term for `FROM-DF`.
`*h4-recipes-recognizers*` is the list of the three recognizer symbols in
the order `DFP`, `RATIONALP`, `STRINGP`.

Pass `:none` for an absent formula. An empty compound formula uses `nil`.
Reading the head of an empty compound produces a failure.
