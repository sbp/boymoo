# Parity tests using halves

A Library, term and Step have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. The constants `*t2-half-parity-two*` and
`*t2-half-parity-neg-half*` are the terms quoting 2 and −1/2.

All calls can return a failure. A call that returns only a Library
is the resulting Library with any added lemmas.
A call that returns a Step and a Library uses `(cons step lib)`.

| ACL2 call | Arguments and result |
|---|---|
| `(t2-half-parity-integer-boolean lib test)` | For an integrality-test term, the Step proving it Boolean. |
| `(t2-half-parity-boolean-complement lib distinct)` | Given a Step denying equality of two integrality tests, a Step equating the left test with the negation of the right, paired with the Library. |
| `(t2-half-parity-alternation-base lib template)` | A Step for the zero case of parity alternation, with the term `template` specifying the occurrences of `X` to restore. |
| `(t2-half-parity-alternation lib)` | Library with `HALF-INTEGRAL-PERIOD` and `HALF-INTEGRAL-ALTERNATES` added in that order, with any auxiliary lemma added at its first use. |
| `(t2-half-parity-cancel-half lib numeric outer inner)` | Given a number Step and two factor terms, a Step cancelling the nested multiplications by those factors. |
| `(t2-half-parity-fold-constants lib source value first second)` | Given a sum term `source`, its retained term `value` and its two constant terms, a Step arranging and evaluating their sum. If the constants sum to zero, the Step also removes that zero. |
| `(t2-half-parity-half-shift lib)` | Library with `HALF-SHIFT-INTEGER-TEST` added. |
| `(t2-half-parity-translate-half-test lib half argument integral)` | Given a halved term, the argument term and its integer Step, a Step relating the integrality of the halved term shifted by 1/2 to the negation of the unshifted test. |
| `(t2-half-parity-sum-parity lib)` | Library with `HALF-INTEGER-SUM-TEST` added. |
| `(t2-half-parity-build lib)` | Library extended by the alternation, half-shift and sum recipes in that order. |
