# Bit mismatch proofs

`lib` is a B1 BookProof as described in `prover/b1/sig/logic.md`. A term
and a Step have the forms specified in `prover/sig/proof.md`. Each proof
operation below may return a failure as its entire result. Where the result
is `(cons value lib)`, its cdr is the library after the proof recipe has
added any auxiliary lemmas. Use that library for the next proof operation.

The symbol constants are `*b1-mismatch-mismatch*`, `*b1-mismatch-max*`,
`*b1-mismatch-logbitp*`, and `*b1-mismatch-oddp*`.

| Call | Arguments and result |
|---|---|
| `(b1-mismatch-mismatch-exists lib formula)` | An equivalence formula with a mismatch call as its first operand. Returns `(cons step lib)` for the formula. |
| `(b1-mismatch-mismatch-bound lib formula)` | An implication bounding the mismatch index by the maximum bit length. Returns `(cons step lib)` for the formula. |
| `(b1-mismatch-mismatch-correct lib formula)` | An implication that the two bit tests differ at the reported index. Returns `(cons step lib)` for the formula. |
| `(b1-mismatch-equal-fixed-by-bits lib formula)` | An implication that fixed integers agree under a bit-agreement hypothesis. Returns `(cons step lib)` for the formula, or `unproved` if no unconditional fact matches the required bit agreement. |
| `(b1-mismatch-mismatch-wrapped-index lib formula)` | An implication about the mismatch index under a wrapper that applies NFIX. Returns `(cons step lib)` for the formula. |

When the BookProof has a search index, call
`(b1-mismatch-equal-fixed-by-bits-with-index lib formula index)` with the
FactIndex described in `prover/b1/sig/search.md`. Its result and failure conditions
are those of `b1-mismatch-equal-fixed-by-bits`, which uses a BookProof
without an index.

## Proof recipes

| Call | Arguments and result |
|---|---|
| `(b1-mismatch-normalized-bit-functions lib term)` | A term. Returns the list of the low-bit and signed high-bit equality Steps, in that order. |
| `(b1-mismatch-bit-join lib term low high)` | A term and its low-bit and high-bit equality Steps. Returns `(cons step lib)` for the reconstruction of its fixed integer. |
| `(b1-mismatch-equality-from-bit-parts lib a b)` | Two terms. Returns `(cons step lib)` for equality of their fixed integers in terms of their two components. |
| `(b1-mismatch-zero-length-values lib term stopped)` | A term and a Step for its zero length. Returns `(cons step lib)` showing its fixed value is zero or minus one. |
| `(b1-mismatch-low-bit-of-fixed-point lib term fixed)` | A term and a Step for its fixed value. Returns `(cons step lib)` for its low bit. |
| `(b1-mismatch-fixed-points-agree lib a b finished low)` | Two terms, a Step for both having zero length, and a Step for agreement of their low bits. Returns `(cons step lib)` for agreement of their fixed values. |
| `(b1-mismatch-natural-mismatch lib call known)` | A mismatch call and a Step that it is true. Returns `(cons step lib)` for its natural-number type. |
| `(b1-mismatch-fixed-sign lib term)` | A term. Returns a Step equating its guarded negative test to the negativity of its fixed integer. |
| `(b1-mismatch-nonnegative-high-bits lib term sign)` | A term and a Step for its guarded nonnegativity. Returns `(cons step lib)` for guarded nonnegativity of the high bits. |
| `(b1-mismatch-max-with-zero lib term-natural active-left parts)` | A natural-number Step, a Boolean selecting its position in the maximum, and a list of evidence Steps. Returns `(cons step lib)` equating the maximum to the term. Pass `nil` for omitted evidence. |
| `(b1-mismatch-maximum-decreases lib recurrence)` | A MismatchInduction. Returns `(cons step lib)` showing that the maximum bit length drops by one when the scan continues. |
| `(b1-mismatch-maximum-length-type lib term)` | A maximum-length term. Returns `(cons step lib)` for its natural-number type. |
| `(b1-mismatch-positive-maximum-length lib term known)` | A maximum-length term and a Step proving that one operand is positive. Returns `(cons step lib)` proving the maximum positive. |
| `(b1-mismatch-immediate-nonnegative-bound lib recurrence maximum signs different)` | A MismatchInduction, its maximum-length term, two guarded nonnegativity Steps in argument order, and a Step showing different low bits. Returns `(cons step lib)` proving the maximum positive. |
| `(b1-mismatch-floor-of-doubled-divisor lib integral divisor-type divisor-positive)` | Steps for an integer numerator, an integer divisor, and positivity of the divisor. Returns `(cons step lib)` equating the two floors. |
| `(b1-mismatch-bit-at-successor lib index-natural term)` | A Step for a natural index and a term. Returns `(cons step lib)` relating the successor bit test to the bit test of the signed high bits. |
| `(b1-mismatch-bit-at-zero lib term)` | A term. Returns `(cons value lib)` with the list of the bit test and low-bit equality Steps, in that order, as its value. |

## Mismatch induction

A MismatchInduction has the form
`(:b1-mismatch-mismatch-induction lib call formula measure substitution child low-match stopped view)`.
`substitution` is an alist of `(variable . term)` bindings in insertion
order, with a new value for a repeated key taking the place of the old one.
The fields `call`, `formula`, `measure`, `child`, `low-match`, and
`stopped` are terms. `view` is the Step opening `call`.

| Call | Arguments and result |
|---|---|
| `(b1-mismatch-mismatch-induction-init lib call formula)` | A library, mismatch call and formula. Returns a MismatchInduction. |
| `(b1-mismatch-mismatch-induction-first induction)` | A MismatchInduction. Returns a Step opening the call for an immediate mismatch. |
| `(b1-mismatch-mismatch-induction-matching induction equal)` | A MismatchInduction and a Step equating the low bits. Returns a Step opening the call when the low bits match. |
| `(b1-mismatch-mismatch-induction-later induction opened)` | A MismatchInduction and its opened matching case Step. Returns a Step continuing the scan. |
| `(b1-mismatch-mismatch-induction-hypothesis induction)` | A MismatchInduction. Returns `(cons step lib)` for its induction hypothesis at the smaller pair. |
| `(b1-mismatch-mismatch-induction-finish induction proof)` | A MismatchInduction and its case Step. Returns `(cons step lib)` applying the induction rule. |

The field accessors take the MismatchInduction and return the named field
directly. Their names use the prefix `b1-mismatch-mismatch-induction-`
followed by the field name. The function with the suffix `with-lib` takes
a MismatchInduction and a library and returns the object with that library.
