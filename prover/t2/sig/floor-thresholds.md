# Floor thresholds

In these calls, `lib` is a Library, a term is prover data, and a Step is a
proof step as specified in `prover/sig/`. The `cases` argument is a
QuotientCases object as specified in `prover/t2/sig/quotient-rounding.md`.
The functions return a failure in place of the result if proof construction
fails. A result that is a Library contains the new lemmas in the order of
their addition.

| ACL2 call | Arguments and result |
|---|---|
| `(t2-floor-thresholds-below-integer lib cases floor)` | The floor term `floor` is compared with the integer threshold `Z`. Return the Library with the threshold lemma. |
| `(t2-floor-thresholds-sign-and-zero lib cases floor)` | Return the Library with the positive and zero tests for the floor term `floor`. |
| `(t2-floor-thresholds-signed-quotient-test lib cases threshold sign increasing)` | Given threshold term `threshold`, strict divisor sign Step `sign`, and Boolean `increasing`, return the two-element list of the normalized comparison Step and the divisor disequality Step. |
| `(t2-floor-thresholds-fixed-zero-floor lib cases zero)` | From the Step `zero` equating the fixed divisor to zero, return a Step equating the floor to zero. |
| `(t2-floor-thresholds-floor-with-zero-ratio lib cases product)` | From the Step `product` equating the quotient to zero, return a Step equating the floor to zero. |
| `(t2-floor-thresholds-no-sign-floor lib cases no-positive no-negative)` | The last two arguments are Steps excluding a positive and a negative divisor, respectively. Return a Step equating the floor to zero. |
| `(t2-floor-thresholds-case-alignment-reduce step lib known)` | Simplify the right side of equality Step `step` with the ordered list `known` of evidence Steps. Return the resulting equality Step. |
| `(t2-floor-thresholds-case-alignment lib left right known tests)` | Align the right sides of equality Steps `left` and `right` using evidence Steps `known` in list order and case-splitting on the terms `tests` in list order. Return an equality Step. Can fail when there are no tests left for an alignment. |
| `(t2-floor-thresholds-express-floor-signs lib cases)` | Return the Library with the positive and negative floor tests expressed in terms of the operands. |
| `(t2-floor-thresholds-impossible-interval lib condition comparison sign)` | Given a strict sign test term, a strict comparison term, and a sign Step for the other endpoint, return the Step equating the guarded comparison to false. |
| `(t2-floor-thresholds-express-floor-zero lib cases)` | Return the Library with the zero floor test expressed in terms of the operands. |
| `(t2-floor-thresholds-build lib)` | Return the Library with the floor threshold and divisor test lemmas. |

The results of `signed-quotient-test`, `fixed-zero-floor`,
`no-sign-floor`, `case-alignment-reduce`, `case-alignment`, and
`impossible-interval` are `(cons value lib)`. The Step or list in the
table is `value`, and `lib` carries any added auxiliary entries.
A failure is the entire result.
