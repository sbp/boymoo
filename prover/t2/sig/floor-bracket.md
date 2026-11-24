# Floor bracket

`lib` is a Library as specified in `prover/sig/library.md`. Terms and Steps
have the forms in `prover/sig/proof.md`. `cases` is a QuotientCases object
as specified in `prover/t2/sig/quotient-rounding.md`. Every function can
return a failure. A function that adds lemmas returns the resulting Library
with entries and facts in insertion order.

| Call | Arguments and result |
|---|---|
| `(t2-floor-bracket-bracket lib)` | Library with the quotient bracket and floor integrality lemmas. |
| `(t2-floor-bracket-rational-mod-at-zero floor-equals-zero lib opened x-type input-type)` | Four Steps, with a Library as the second argument. Returns the remainder rationality Step for the zero-floor case. |
| `(t2-floor-bracket-rational-mod lib cases i-floor opened)` | Given the floor integrality Step `i-floor` and the remainder definition equality Step `opened`, returns the Library with the rational dividend remainder lemma. |
| `(t2-floor-bracket-signed-divisor lib known-sign)` | `known-sign` is a strict sign Step for the divisor. Returns a three-element list of Steps, in order, for fixed divisor nonzero, divisor numeric, and unfixed divisor nonzero. |
| `(t2-floor-bracket-remainder-identity lib q f known-sign)` | `q` and `f` are the quotient and floor terms and `known-sign` is the strict sign Step. Returns the three Steps for the scaled-difference identity, divisor numeric, and unfixed divisor nonzero, in that order. |
| `(t2-floor-bracket-remainder-bounds lib cases floor-integer)` | Given the integrality Step for the floor, returns the Library with positive-then-negative divisor remainder bounds. |
| `(t2-floor-bracket-build lib)` | Library extended with the floor bracket and remainder lemmas. |
