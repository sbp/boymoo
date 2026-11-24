# Dyadic descent

`lib` is the library used by the T2 arithmetic tactics. Terms and Steps use
the shared proof representation. Definitions and Calls use the shared
termination representation. `*t2-dyadic-two*` is the term for quoted 2.

| Call | Result | Failure |
|---|---|---|
| `(t2-dyadic-twice value)` | Product term for two times `value`. | None. |
| `(t2-dyadic-half value)` | Product term for one half times `value`. | None. |
| `(t2-dyadic-low-gap value)` | Difference term for the denominator minus the numerator. | None. |
| `(t2-dyadic-high-gap value)` | Difference term for the numerator minus the denominator. | None. |
| `(t2-dyadic-measure value)` | Count of the numerator and denominator gap, selected by the comparisons with 1 and 2. | None. |
| `(t2-dyadic-cancel-scales lib value is-rational first second)` | Step cancelling the two scales `first` and `second` on `value`, whose rationality is given by `is-rational`. | A proof failure. |
| `(t2-dyadic-pos-product lib scale is-rational is-positive)` | Positivity Step for the product of the term `scale` and the positive rational described by the two input Steps. | A proof failure. |
| `(t2-dyadic-positive-numerator lib rat positive-value pos-d int-d)` | Positivity Step for the numerator, given Steps for rationality, positivity and the denominator's positivity and integrality. | A proof failure. |
| `(t2-dyadic-reduced-parts-move lib rat positive-value)` | Four values comprising the weak denominator bound, weak numerator bound, list of integrality Steps, and rationality Step for the doubled value, in that order. | A proof failure. |
| `(t2-dyadic-strict-gap-order lib)` | Library with the two gap comparison lemmas. | A proof failure. |
| `(t2-dyadic-positive-gap lib is-rational order)` | Two-element list of the positivity Step and the list of numerator and denominator integrality Steps. | A proof failure. |
| `(t2-dyadic-rank-value lib value conditions)` | Step evaluating the uncounted measure under the ordered list of condition Steps. | A proof failure. |
| `(t2-dyadic-rank-count lib expansion gap types)` | Step evaluating the count using `expansion`, optional gap Step `gap` and integrality Steps `types`. Pass `nil` for either omitted argument. | A proof failure. |
| `(t2-dyadic-ordinal-rank lib smaller greater difference)` | Ordinal comparison Step from two expansion Steps and a strict comparison Step. | A proof failure. |
| `(t2-dyadic-doubling lib rat pos)` | Library with the doubling decrease lemma. | A proof failure. |
| `(t2-dyadic-above-one lib is-rational at-least-two)` | Step proving that the rational is greater than 1 from its weak lower bound of 2. | A proof failure. |
| `(t2-dyadic-halving lib rat pos)` | Library with the halving decrease lemma. | A proof failure. |
| `(t2-dyadic-build lib)` | Library with the gap comparison and decrease lemmas in recipe order. | A proof failure. |
| `(t2-dyadic-definition lib definitions calls)` | Measure proof entry, or `nil` if the definition and calls do not match. The entry uses the distinct obligations in the order of their first occurrence. | A failure if a decrease lemma fails to establish an ordinal comparison or a proof operation fails. |

The results of `t2-dyadic-positive-numerator`,
`t2-dyadic-reduced-parts-move`, `t2-dyadic-rank-count` and
`t2-dyadic-above-one` are `(cons value lib)`, with the Step or list in
the table as `value`. The library carries any auxiliary lemmas added
during the call. A failure is the entire result.
