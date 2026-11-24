# Bounds for bitwise conjunction

Terms, Steps, and the Library have the forms in `prover/sig/proof.md` and
`prover/sig/library.md`. A pair is `(cons value library)` with the resulting
Library. A failure is the entire result. Each `types` argument is a list of
integer evidence Steps in the order supplied. Every function can return a failure
when reading its inputs or constructing the proof.

| Call | Result |
|---|---|
| `(b2-logand-nonnegative-difference library weak)` | The nonnegative difference Step for the weak comparison Step `weak`. |
| `(b2-logand-weak-chain library left right types)` | The composed weak comparison Step for Steps `left` and `right`. |
| `(b2-logand-weak-shift library bound amount types)` | The weak comparison Step for both sides of Step `bound` shifted by term `amount`. |
| `(b2-logand-distinct-bound library weak different types)` | The strict comparison Step for weak comparison Step `weak` and distinctness Step `different`. |
| `(b2-logand-odd-lower-bound library upper odd quotient quotient-type types)` | The weak lower bound for the odd term given Steps `upper` and `odd`, quotient term `quotient` and integer Step `quotient-type`. |
| `(b2-logand-logand-bounds library)` | A pair with the bounds lemma name and the Library containing it. |
| `(b2-logand-prove-logand library name formula)` | A pair with the Step proving the given bound formula for theorem symbol `name`. |

`*b2-logand-logand*` and `*b2-logand-even*` are the symbols `BINARY-LOGAND`
and `COMMON-LISP::EVENP`. `*b2-logand-two*` is the quotation of `2`.
