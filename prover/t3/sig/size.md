# Bounds on structural measures and ordinal rankings

`lib` is a Library with the T3 proof rules for its dispatch tag. Terms and Steps
have the forms in `prover/sig/proof.md`. `integers` is a list of Steps in
evidence order. `evidence` is a T3 Evidence object. The constants are
`*t3-size-make-ord*`, `*t3-size-o-finp*`, `*t3-size-o-first-expt*`,
`*t3-size-o-first-coeff*`, `*t3-size-o-rst*`, `*t3-size-posp*`,
`*t3-size-evens*`, `*t3-size-odds*`, `*t3-size-ordinal-operations*` and
`*t3-size-w*`.

A result described as a Step and a single updated object is `(cons step object)`.
A result described as a Step, Library and Evidence is `(list step lib evidence)`.
Evidence keeps its facts in insertion order. A failure replaces the whole result.
An empty selector path is `nil`. A missing selector path is `:none`.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t3-size-build lib)` | Library extended with the general size lemmas in source order. | A failure from constructing or adding a lemma. |
| `(t3-size-endpoints proof)` | Endpoints of the comparison in Step `proof`, as a list in increasing order. | A failure from reading the Step or a malformed comparison. |
| `(t3-size-chain lib lower upper integers)` | Step composing comparison Steps `lower` and `upper` with a common endpoint. Pass `nil` for omitted integers. | A failure from constructing a Step, or `proof-mismatch` for unequal middle terms. |
| `(t3-size-shift lib proof offset prefix integers)` | Step adding term `offset` to both sides of comparison Step `proof`. Pass `nil` for the default suffix position and `t` for the prefix position. Pass `nil` for omitted integers. | A failure from constructing a Step. |
| `(t3-size-sum-at-least lib included other-nonnegative integers prefix)` | Step bounding the sum of term `included` and the nonnegative term proved by Step `other-nonnegative` below by `included`. Pass `nil` for omitted integers and `t` for the default prefix position. | A failure from constructing a Step. |
| `(t3-size-selector-path child parent)` | List of successive CAR or CDR calls, starting at term `child` and stopping before term `parent`. Returns `nil` when the terms agree and `:none` when no path exists. | `missing-proof-input` for a selector without an argument. |
| `(t3-size-count-bound lib child parent evidence)` | Count comparison Step for child and parent terms, with the updated Evidence. | `unsupported` for a missing path, or a failure from evidence or proof construction. |
| `(t3-size-count-descent lib smaller larger evidence)` | Ordinal decrease Step for count terms `smaller` and `larger`, with the updated Evidence. | `unsupported` for a missing strict decrease, `fuel` on exhaustion, or a failure from evidence or proof construction. |
| `(t3-size-phase-count measure)` | Count term inside doubled measure term `measure`, with or without a phase, or `nil` when unmatched. | A failure for a malformed sum or product. |
| `(t3-size-doubled-rank base phase)` | Doubled term `base`, plus one when Boolean `phase` is true. | None. |
| `(t3-size-phase-lemma lower upper)` | Lemma name for Boolean phases `lower` and `upper`. | None. |
| `(t3-size-ordinal-doubled lib measure)` | Ordinality Step for doubled measure term `measure`. | A failure from proof construction. |
| `(t3-size-doubled-descent lib smaller larger evidence transformed)` | Decrease Step for doubled measure terms, Library and Evidence. Pass `nil` for the default without a transformed bound or `t` to request the transformed bound if needed. | `unsupported` for incompatible phases or unavailable bounds, or a failure from evidence or proof construction. |
| `(t3-size-doubled-descent-from-bound lib smaller larger evidence size)` | Resume doubled descent with comparison Step `size` from the transformed-bound function and the resulting Library and Evidence. Returns the Step, Library and Evidence. | A failure from evidence or proof construction. |
| `(t3-size-len-cons lib car-term cdr-term)` | Step unfolding the length of a cons of the two given terms. | A failure from proof construction. |
| `(t3-size-length-tail lib term evidence)` | Strict length comparison Step for the tail of `term`, with the updated Evidence. | A failure from evidence or proof construction. |
| `(t3-size-length-weak lib)` | Library extended with the weak CDR length lemma. | A failure from constructing or adding the lemma. |
| `(t3-size-evens-bounds lib)` | Library extended with the weak CDR length lemma and the EVENS length lemma. | A failure from constructing or adding a lemma. |
| `(t3-size-evens-step lib bound term evidence)` | Length comparison Step for EVENS of `term` from comparison Step `bound` at its tail, with the updated Evidence. | A failure from evidence or proof construction. |
| `(t3-size-alternating-length lib smaller larger evidence)` | Length comparison Step for an alternating projection, Library and Evidence. | `unsupported` for an unknown projection, or a failure from evidence or proof construction. |
| `(t3-size-constructors lib measure)` | Two CONSP Steps for the unit-exponent ordinal constructor in `measure`, in inner-to-outer order. | A failure from a malformed measure or proof construction. |
| `(t3-size-ordinal-with-phase coefficient phase)` | Unit-exponent ordinal using the given coefficient and finite phase terms. | None. |
| `(t3-size-open-ordinal-order lib left right evidence)` | Step unfolding the ordinal comparison between terms `left` and `right`. Here `evidence` is a list of Steps, with `nil` for the default. | A failure from proof construction. |
| `(t3-size-ordinal-ranking-lemmas lib)` | Library with the unit-exponent ordinal lemmas available, adding them in source order when needed. | A failure from constructing or adding a lemma. |
| `(t3-size-ordinal-phase lib measure)` | Ordinality Step for measure term `measure`, with the updated Library. | `unsupported` for an unsupported ranking or coefficient, or a failure from proof construction. |
| `(t3-size-coefficient-descent lib smaller larger order)` | Ordinal decrease Step for unit-exponent measures with strict coefficient comparison Step `order`, with the updated Library. | A failure from proof construction. |
| `(t3-size-phase-descent lib smaller larger order)` | Ordinal decrease Step for unit-exponent measures with equal coefficients and strict phase comparison Step `order`, with the updated Library. | A failure from proof construction or unequal coefficients. |
| `(t3-size-sum-count lib after before evidence)` | Count-sum comparison Step for sum terms `after` and `before`, with the updated Evidence. Tries the components in the listed order before trying the reversed order. | `unsupported` for missing selector paths or unsupported coefficients, or a failure from proof construction. |
| `(t3-size-ordinal-descent lib smaller larger evidence)` | Ordinal decrease Step for unit-exponent measures, Library and Evidence. | `unsupported` when the coefficient need not decrease, a failure for unexpected coefficients, or a failure from proof construction. |

With `transformed` true, doubled descent can return
`(:t3-size-transformed child parent evidence)` in place of its ordinary
result. The fields are the arguments to the bound function after `lib`.
Use the returned Step and objects in `t3-size-doubled-descent-from-bound`,
or propagate the bound function's failure.

`(t3-size-ordinal-comparison lib a b)` returns the finite-order equality
Step for terms `a` and `b`, using the T3 integer proof for each. It can
return a failure from proof construction.
