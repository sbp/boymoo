# Round ties

`lib` is a Library as specified in `prover/sig/library.md`. Terms and Steps
have the forms in `prover/sig/proof.md`. `cases` is a QuotientCases object
as specified in `prover/t2/sig/quotient-rounding.md`. Tests and known evidence
are lists of Steps in argument order. Every function can return a failure.

The symbol datum `ROUND` is `*t2-round-ties-round*`.

| Call | Arguments and result |
|---|---|
| `(t2-round-ties-replace-body lib step equality)` | `step` and `equality` are equality Steps. Returns `step` with the left side of `equality` rewritten throughout the right side of `step`. |
| `(t2-round-ties-conditional-equation-choose tests lib left right known)` | Simplifies the right sides of the Steps `left` and `right` under `known` followed by `tests`. Returns their combined equality Step. |
| `(t2-round-ties-conditional-equation lib left right below above known tie)` | `left` and `right` are Steps and `below` and `above` are strict comparison terms. Pass `nil` for omitted `known` and `:none` for an absent `tie` term. Returns the equality Step from the strict and tied cases. |
| `(t2-round-ties-integral-floor lib cases tests unit)` | `unit` is the unit-divisor floor equality Step. Returns the integer Step for the floor in the supplied case. |
| `(t2-round-ties-unit-remainder lib ratio unit integral)` | `ratio` is a quotient term, `unit` is the unit-divisor floor equality Step, and `integral` is the floor's integer Step. Returns the Step expanding the remainder of the ratio by one. |
| `(t2-round-ties-round-branch lib opened tests)` | Simplifies the right side of equality Step `opened` under `tests` and returns the chained Step. |
| `(t2-round-ties-negative-shift lib ratio floor increment)` | For quotient, floor and increment terms, returns the Step expressing the ratio minus the increment as the ratio minus the floor minus one. |
| `(t2-round-ties-rational-round lib cases opened expected tests)` | `opened` is the expanded rounding equality Step and `expected` is the rounding formula term. Returns the Step for a rational quotient case. |
| `(t2-round-ties-nonrational-round lib cases opened expected not-rational)` | With the same `opened` and `expected` arguments and the negated rationality Step `not-rational`, returns the Step for a nonrational quotient. |
| `(t2-round-ties-build-branch tests lib cases opened expected)` | Returns the appropriate rational or nonrational rounding Step for the supplied test Steps. |
| `(t2-round-ties-build lib)` | Library extended with the round-by-floor lemma. |

The nonrational rounding recipe and the lifted build branch return
`(cons step lib)`. The Library includes any strict-comparison lemma added
while proving the branch. A failure is the entire result.
