# Measures for recursive definitions

`lib` is a B2 tactics library. Terms and Steps follow `prover/sig/proof.md`.
A definition is `(name formals body)` and Calls follow
`prover/sig/termination.md`. `aids` is an association list of
`(function-name . measure-term)` entries.

A B2 Rulers object has the form `(:b2-measures-rulers lib steps)`. The
`steps` table maps literals to Steps and retains first-insertion order,
including any evidence established by queries. A query returns its Step or
`nil` paired with the resulting Rulers. Use the accessors for its fields.

| Call | Result | Failure |
|---|---|---|
| `(b2-measures-rulers-init lib evidence)` | Rulers with the evidence Steps expanded by the library's evidence routine. | Failure from collecting evidence. |
| `(b2-measures-rulers-lib rulers)` | The library. | — |
| `(b2-measures-rulers-steps rulers)` | The ordered evidence table. | — |
| `(b2-measures-rulers-find rulers term)` | `(cons step rulers)` for `term`, with a missing step represented by `nil`. | Failure from deriving evidence. |
| `(b2-measures-rulers-require rulers term)` | `(cons step rulers)` for `term`. | `Unproved` when the step is missing, or a failure from deriving evidence. |
| `(b2-measures-rulers-direct-builtin lib clause rulers)` | `(cons step rulers)` for a built-in instance of `clause`, with `nil` for no match. | Failure from matching or deriving evidence. |
| `(b2-measures-rulers-selector-decrease lib goal rulers)` | `(cons step rulers)` for selector decrease term `goal`. | Failure from deriving evidence or proving the decrease. |
| `(b2-measures-strict-count lib smaller parent rulers)` | `(cons step rulers)` for the strict size decrease from `parent` to `smaller`. | Failure from deriving evidence or proving the decrease. |
| `(b2-measures-set-tail-decrease lib value nonempty)` | A Step for the size decrease from ordered-set term `value` to its tail using Step `nonempty`. | Failure from the proof. |
| `(b2-measures-measure-natural lib term)` | A Step proving the measure term natural. | Failure from the proof. |
| `(b2-measures-ordinal lib term)` | A Step proving the measure term ordinal. | Failure from the proof. |
| `(b2-measures-integer-measure lib term evidence)` | A Step proving the measure term integer under the evidence Steps. | Failure from the proof. |
| `(b2-measures-finite-order lib smaller parent evidence)` | A Step equating ordinal and integer ordering of the two terms under the evidence Steps. | Failure from the proof. |
| `(b2-measures-compare-sum n lib smaller parent evidence)` | `(cons step lib)` with a Step comparing the sum measures under the evidence Steps and the resulting library. Pass natural-number fuel `1000000` at the top. | `Unproved` if the sum is unchanged, a failure from the proof, or `Fuel`. |
| `(b2-measures-unfold-measure lib term)` | An unfolding Step for the measure when it unfolds to a sum, or `nil`. | Failure from unfolding. |
| `(b2-measures-compare n lib goal evidence)` | `(cons step lib)` with a Step proving the comparison term `goal` under the evidence Steps and the resulting library. Pass natural-number fuel `1000000` at the top. | `Unproved` when there is no comparison proof, a failure from the proof, or `Fuel`. |
| `(b2-measures-plans definitions calls aids)` | The ordered list of candidate measure tables, with each table in the order of insertion. | Failure from reading definitions, Calls or measures. |
| `(b2-measures-prove-measure lib definitions calls aids)` | `(cons entry lib)` with the first successful measure proof entry and the resulting library. The entry follows `proof-proof-entry`. | `Unproved` when all candidates fail, or a failure from planning or building the entry. |

The symbol constants are `*b2-measures-nfix*`, `*b2-measures-zp*`,
`*b2-measures-set-empty*`, `*b2-measures-set-fix*`,
`*b2-measures-set-tail*` and `*b2-measures-setp*`.
