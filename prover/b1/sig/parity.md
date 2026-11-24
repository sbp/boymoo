# Parity

Terms, symbols and Steps use the forms in `prover/sig/proof.md`. A Library
has the form in `prover/sig/library.md`. A result written `(cons value lib)`
carries the Library after any auxiliary lemmas have been added. On a
failure, that value is the entire result.

`*b1-parity-half*` is the term quoting one half. `*b1-parity-r*` and
`*b1-parity-i*` are the prover symbols `R` and `I`.

| Call | Result | Failure |
|---|---|---|
| `(b1-parity-half term)` | The product term for one half times `term`. | None. |
| `(b1-parity-either-half lib formula integer-half)` | A Step proving the conditional disjunction `formula` from a Step for either alternative. | A failure from proof construction. |
| `(b1-parity-parity-case lib negative)` | `(cons name lib)` for the consecutive-integer halves lemma on naturals or their negatives. `negative` is a Boolean. | A failure from proof construction. |
| `(b1-parity-half-or-previous lib i int-i)` | `(cons step lib)` for the disjunction that `i` or `i - 1` has an integer half, given the term `i` and its integer Step. | A failure from proof construction. |
| `(b1-parity-power-type lib name base exponent evidence)` | The Step obtained from the fact with unqualified name string `name`, the base and exponent terms, and the ordered list of evidence Steps. | A failure from proof construction. |
| `(b1-parity-even-power-positive lib formula)` | `(cons step lib)` for the positive even power of a negative rational base, given the implication term `formula`. | A failure from proof construction. |
| `(b1-parity-odd-power-negative lib formula)` | `(cons step lib)` for the negative odd power of a negative rational base, given the implication term `formula`. | A failure from proof construction. |
| `(b1-parity-adjacent-half-equation lib greater lesser int-x)` | A Step equating the half of `greater` to the half of `lesser` plus one half, given consecutive exponent terms and the integer Step for their variable. | A failure from proof construction. |
| `(b1-parity-adjacent-halves-cannot-both-be-integers lib high low equation test)` | `(cons step lib)` with the contradiction of the two integer halves, given Steps `high`, `low` and `equation` and the integer test term `test`. | A failure from proof construction. |
| `(b1-parity-negated-base-case lib direction)` | `(cons name lib)` for the sign rule at the nonnegative or nonpositive exponents. `direction` is the term quoting 1 or -1. | A failure from proof construction. |
| `(b1-parity-sign-rule lib base integer-i numeric nonzero)` | `(cons step lib)` for the sign rule with base term `base`, an integer exponent Step and Steps for a numeric and nonzero base. | A failure from proof construction. |
| `(b1-parity-negate-fixed-zero lib base fix-zero)` | A Step equating the negation of `base` to zero, given the Step equating its `FIX` to zero. | A failure from proof construction. |
| `(b1-parity-negated-base lib formula)` | `(cons step lib)` for the requested sign of an integer power of a negated base, given the implication term `formula`. | A failure from proof construction. |
