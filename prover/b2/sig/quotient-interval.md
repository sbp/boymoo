# Quotient interval

`lib` is the B2 tactic library. Terms and Steps have the forms in
`prover/sig/proof.md`. The constant `*b2-quotient-interval-force*` is the
prover symbol for `FORCE`.

Each call can return a failure in place of its result. A result of the form
`(cons value lib)` carries the library after any lemma additions.

| ACL2 call | Arguments and result |
|---|---|
| `(b2-quotient-interval-quotient-data lib i j typed-i nonnegative-i typed-j positive-j)` | The terms `i` and `j`, with Steps for integrality of `i`, nonnegativity of `i`, integrality of `j`, and positivity of `j`. Returns `(cons (list q-int lower upper) lib)` with integrality of the quotient and its lower and upper bounds. |
| `(b2-quotient-interval-shift-bound lib upper)` | The strict upper bound Step from `quotient-data`. Returns the shifted comparison Step. |
| `(b2-quotient-interval-ratio-is-integer lib q ratio q-int lower upper)` | The quotient and ratio terms, then the three Steps from `quotient-data` in result order. Returns the Step equating quotient exactness and ratio integrality. |
| `(b2-quotient-interval-quotient-signs lib i j typed-i typed-j positive-j)` | The dividend and divisor terms, their integer Steps, and the positive divisor Step. Returns `(cons (list zero-test positive-test) lib)`. |
| `(b2-quotient-interval-niq-theorem lib name formula)` | A theorem name symbol and its formula. Returns `(cons step lib)`. |

The implication in `niq-theorem` uses the library's evidence in first key
insertion order when collecting `FORCE` premises.
