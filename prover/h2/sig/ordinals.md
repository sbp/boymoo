# Ordinal constructors and order

`proof` is the H2 proof context. Terms, bindings and Steps use the forms
in `prover/sig/proof.md`. A result described as `(cons value proof)` includes
the resulting proof context, with any added lemmas and changed search rules.
A failure from proof construction is the entire result of any call below.

| Function and arguments | Result |
|---|---|
| `(h2-ordinals-natural-fix proof value)` | `(cons step proof)` with the Step proving `NFIX` of term `value` natural. |
| `(h2-ordinals-noncons-fix proof value)` | `(cons step proof)` with the Step proving `NFIX` of term `value` is an atom. |
| `(h2-ordinals-integer-fix proof value)` | `(cons step proof)` with the Step proving `NFIX` of term `value` an integer. |
| `(h2-ordinals-successor-facts proof natural)` | Two Steps in order, for integrality and positivity of one plus the term proved natural by `natural`. |
| `(h2-ordinals-ordinal-constructor proof)` | `(cons name proof)` with the name string of the ordinal constructor lemma. |
| `(h2-ordinals-constructor-ordinal proof value exponent-int exponent-positive coefficient rest comparison)` | `(cons step proof)` with the ordinality equality for constructor term `value`. `exponent-int`, `exponent-positive`, `rest` and `comparison` are Steps. `coefficient` is the list of integer and positive Steps for the coefficient, in that order. |
| `(h2-ordinals-pair-ordinal proof formula)` | `(cons step proof)` proving the ordinality of the pair measure in `formula`. |
| `(h2-ordinals-positive-length proof cons-step)` | Two Steps in order, for integrality and positivity of the length of the argument that `cons-step` proves is a cons. |
| `(h2-ordinals-list-ordinal proof formula)` | `(cons step proof)` proving the ordinality of the list measure in `formula`. |
| `(h2-ordinals-comparison-rules proof)` | `(cons names proof)` with the comparison rule names as strings in citation order. |
| `(h2-ordinals-pair-order proof formula)` | `(cons step proof)` proving the comparison equation for the pair measure. |
| `(h2-ordinals-list-order-branch first-cons second-cons proof not-nil inputs tests rules goal)` | `(cons step proof)` proving `goal` under the Boolean cons assumptions `first-cons` and `second-cons`. `not-nil` is the Step for the value of `(not 'nil)`, `inputs` and `tests` are the two inputs and their cons tests in order, and `rules` is the comparison rule list. |
| `(h2-ordinals-list-order proof formula)` | `(cons step proof)` proving the comparison formula for the list measure. |
| `(h2-ordinals-measure-theorem proof label formula)` | `(cons step proof)` proving the ordinal theorem with name string `label` and claim term `formula`. `step` is `nil` for an unrecognized label. |

The proof context is the inherited Recipes object described in
`prover/h2/sig/recipes.md`. A proof search can return the Search method request
from `prover/h2/sig/search.md` as its entire result. A successful search leaves
the unconsumed replies in the returned Recipes.

| Shared helper and arguments | Result |
|---|---|
| `(h2-ordinals-has-fact proof name)` | The Library's fact entry for symbol `name`, or `nil` if absent. No failure. |
| `(h2-ordinals-search proof method args)` | `(cons value proof)` for the Search operation keyword `method` on argument list `args`, with the unused replies. May return a failure or request. |
| `(h2-ordinals-derive proof formula definitions facts seeds split-limit)` | `(cons step proof)` after configuration from the definition name string `definitions`, ordered fact names `facts`, seed Steps `seeds`, and the split limit. May return a failure or request. |
| `(h2-ordinals-folded-recipe proof fixed name formula definitions facts seeds split-limit)` | Like `derive`, with the additional fixed call terms in `fixed` kept folded for this search. A name string in `name` selects `auxiliary` and returns its fact name in the value position. May return a failure or request. |
| `(h2-ordinals-select-body proof opening evidence)` | The selected equation Step for the opening and evidence Steps, or a failure. |
