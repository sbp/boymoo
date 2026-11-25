# Arithmetic cancellation

Names and terms use the representation in `prover/sig/proof.md`. The `lib`
argument is the B2 Tactics library. Evidence is a list of Steps in argument
order. `*b2-meta-cancel-meta-cancellation*` is the set of the three supported
theorem names, ordered by their S-expression text. The constants
`*b2-meta-cancel-add-equal*`, `*b2-meta-cancel-add-less*` and
`*b2-meta-cancel-multiply-equal*` are the names individually.

| Function | Arguments in order | Result |
|---|---|---|
| `b2-meta-cancel-prove-meta-cancel` | `lib`, theorem name, formula term | `(cons step lib)` with the proof of the formula and the library including the fold definition and auxiliary lemmas |

A Cancellation uses the form `(:b2-meta-cancel-cancellation lib formula term cancel relation fold operands operator fringes fallback openers)`. `fold`
is an ArithmeticFold from `prover/b2/sig/meta-fold.md`. `operands`, `fringes`
and `openers` keep the order given by the formula and the constructor. Use
`b2-meta-cancel-cancellation-init` to construct the object and the functions
with that prefix and the field name to read its fields.

| Function suffix after `b2-meta-cancel-cancellation-` | Arguments after the object in order | Result |
|---|---|---|
| `init` | `lib`, formula, operation symbol, Boolean `less` (constructor takes no object) | Cancellation for the formula |
| `cancel-equation` | evidence | Step opening the cancellation definition |
| `unchanged` | evidence | Step proving the unchanged formula |
| `old-values` | evidence | Step interpreting the initial relation |
| `actual-fringe` | term, evidence | `(cons step cancellation)` with the interpreted fringe equality |
| `equal-shift` | common term, left term, right term, left numeric Step, right numeric Step, common numeric Step or `nil` | `(cons step cancellation)` with the Step removing the common operand from an equality |
| `normalized-relation` | syntax term, ordered list of two fringe residues or `:none` entries, evidence | `(cons step cancellation)` with the evaluated relation |
| `transport-to-result` | original Step, changed Step, evidence | Step relating the initial and cancellation results |
| `both` | evidence | `(cons step cancellation)` for two matching operands |
| `single-less` | operand position, difference Step, remainder term, other term, evidence | `(cons step cancellation)` for one matching operand in a strict comparison |
| `single-equal` | operand position, difference Step, remainder term, other term, evidence | `(cons step cancellation)` for one matching operand in an equality |
| `one` | operand position, evidence | `(cons step cancellation)` for one matching operand |
| `prove` | no further arguments | `(cons step cancellation)` after installing the fold and proving the formula |

Positions in the operand list are zero-based. The constructor and proof
functions can return a failure instead of the result, including `unproved`
when a required cancellation equation is unavailable.

`equal-shift` carries the step and the resulting Cancellation as
`(cons step cancellation)`. Multiplicative cancellation can add auxiliary
lemmas through the common-operand recipe.

`(b2-meta-cancel-cancellation-cons-operation self term operation evidence prove)`
returns `(cons step cancellation)` or a failure. The `prove` recipe identifier
is `:relation`, `:left`, or `(:right first)`, where `first` is the Boolean
result of the left operand test. The callbacks receive their signed evidence
in branch order.
