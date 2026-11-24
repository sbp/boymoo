# Powers

A term, symbol, and Step have the forms specified in `prover/sig/proof.md`. The
`lib` argument is a Library as specified in `prover/sig/library.md`. Evidence is
a list of Steps in the order given by the caller. A result described as a pair
is `(cons value lib)` with the resulting Library. A failure is the entire result.

`*b2-powers-expt*`, `*b2-powers-zip*`, `*b2-powers-zp*`, `*b2-powers-i*`,
and `*b2-powers-j*` are prover symbols.

| Function | Arguments in order | Result | Failure |
|---|---|---|---|
| `b2-powers-expt` | Base term, exponent term | Exponentiation term | — |
| `b2-powers-and-terms` | List of terms in conjunction order | Right-nested conjunction of the terms | Empty term list |
| `b2-powers-zero-from-signs` | Library, term, integer Step, nonnegativity Step, nonpositivity Step | Step equating the term to zero | May return a failure |
| `b2-powers-integer-count` | Library, term, integer Step, signed comparison Step | Step opening the count of an integer | May return a failure |
| `b2-powers-negated-count` | Library, term, integer Step | Pair with the Step equating the counts of the negated term and the term | May return a failure |
| `b2-powers-below-zero-count` | Library, term, integer Step, negativity Step | Pair with the Step proving a strict decrease in count on increment | May return a failure |
| `b2-powers-exp-number` | Library, base term, exponent term | Pair with the Step proving the power numeric | May return a failure |
| `b2-powers-open-nonzero-expt` | Library, base term, exponent term, integer Step for the exponent, sign Step for the exponent, numeric Step for the base, nonzero Step for the base | Step opening the power, or `nil` if unchanged | May return a failure |
| `b2-powers-successor` | Library, base term, exponent term, integer Step for the exponent, numeric Step for the base, nonzero Step for the base | Pair with the successor power Step | May return a failure |
| `b2-powers-predecessor` | Library, base term, exponent term, integer Step for the exponent, numeric Step for the base, nonzero Step for the base | Pair with the predecessor power Step | May return a failure |
| `b2-powers-expt-add-lemma` | Library | Pair with the name of the exponent addition lemma | May return a failure |
| `b2-powers-expt-add` | Library, theorem name symbol, theorem formula | Pair with the Step proving the formula | May return a failure |

`(b2-powers-linear-equal lib left right types)` proves equality of two sums
using the repeated linear cancellation of `b2-tactics-tactics-linear-form`. The last
argument is an ordered list of integer Steps. It can return a failure.

`(b2-powers-evidence-step evidence term)` reads the Step for `term` from
the evidence map and returns a failure if the term is missing.
