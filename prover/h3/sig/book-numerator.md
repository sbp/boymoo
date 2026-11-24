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
| `(h3-book-numerator-positive-reciprocal lib rational positive)` | Given rationality and positivity Steps, returns `(cons step lib)` proving the reciprocal positive. |
| `(h3-book-numerator-numerator-sign lib rational orientation)` | Given a rationality Step and orientation, returns `(cons step lib)` for the comparison with zero through the numerator. |
| `(h3-book-numerator-integer-components lib integer)` | Given an integer Step, returns the list of two equality Steps for the numerator and denominator of its term, in that order. |
| `(h3-book-numerator-num-nonzero-forward lib formula)` | Returns `(cons step lib)` proving the implication from nonzero numerator. |
| `(h3-book-numerator-numerator-theorem lib name formula)` | Returns `(cons step lib)` with the selected rational-component proof or `nil` for an unrecognized name. |
| `(h3-book-numerator-reciprocal-sign lib formula orientation)` | Returns `(cons step lib)` proving preservation of the indicated sign by reciprocation. |
| `(h3-book-numerator-denominator-one lib formula)` | Returns `(cons step lib)` proving the characterization of denominator one. |
| `(h3-book-numerator-reconstruct-numerator lib formula)` | Returns `(cons step lib)` proving reconstruction of the numerator from the denominator and rational. |

`*h3-book-numerator-prefix*` is the rational lemma name prefix.
`*h3-book-numerator-numerator-signs*` is the alist from theorem names to
orientations in source order.

The `-with-library` forms of `positive-reciprocal`, `numerator-sign`,
`num-nonzero-forward`, `numerator-theorem`, `reciprocal-sign`,
`denominator-one` and `reconstruct-numerator` take the same arguments.
They return `(cons value lib)` with any failure as `value`, so a caller can
continue with the Library when it catches the failure.
