# Numerator and denominator proofs

`lib` is a Library. Terms and Steps use the forms in `prover/sig/proof.md`.
`name` is a theorem name string. An `orientation` is `-1` for less than
zero, `0` for equal to zero, or `1` for greater than zero.

Every function below can return a failure in place of its result. A result
written `(cons value lib)` contains the value and the Library with any
auxiliary lemmas, in the order in which they were added. Read the Library
from that pair even when the value is `nil`.

| ACL2 call | Arguments and result |
|---|---|
| `(h3-book-numerator-as-rational lib integer)` | Returns the rationality Step for the term in the integer Step. |
| `(h3-book-numerator-denominator-data lib rational)` | Given a rationality Step, returns the list of Steps for the denominator's and numerator's integrality, the denominator's positivity, and rational reconstruction, in that order. |
| `(h3-book-numerator-integer-components lib integer)` | Given an integer Step, returns the list of two equality Steps for the numerator and denominator of its term, in that order. |

`*h3-book-numerator-prefix*` is the rational lemma name prefix.
`*h3-book-numerator-numerator-signs*` is the alist from theorem names to
orientations in source order.

The `-with-library` forms of `positive-reciprocal`, `numerator-sign`,
`num-nonzero-forward`, `numerator-theorem`, `reciprocal-sign`,
`denominator-one` and `reconstruct-numerator` take the same arguments.
They return `(cons value lib)` with any failure as `value`, so a caller can
continue with the Library when it catches the failure.
