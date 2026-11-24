# Modular exponentiation

`lib` is a B1 Library and `ring` is a Modulus as specified in
`prover/b1/sig/modular.md`. Terms and Steps follow `prover/sig/proof.md`.
Each call can return a failure in place of its entire result. Where the Library
may gain auxiliary lemmas, the result is `(cons value lib)` with the
resulting Library.

| ACL2 call | Result |
|---|---|
| `(b1-mod-expt-guarded conditions)` | A conjunction of the condition terms in their given order. An empty list gives a failure. |
| `(b1-mod-expt-type-nat lib natural)` | The integrality Step given a naturality Step. |
| `(b1-mod-expt-next-natural lib natural)` | The naturality Step for one plus the term of the naturality Step `natural`. |
| `(b1-mod-expt-twice-natural lib natural)` | The naturality Step for twice the term of the naturality Step `natural`. |
| `(b1-mod-expt-step-natural lib integral natural)` | The exponentiation equality at a natural successor, with the resulting Library. `integral` proves the base integral and `natural` proves the predecessor exponent natural. |
| `(b1-mod-expt-integer-power lib integral natural)` | The integrality Step for exponentiation of an integer to a natural exponent, with the resulting Library. The arguments after `lib` are the base and exponent evidence Steps. |
| `(b1-mod-expt-mod-lift ring equality)` | The equality Step obtained by lifting Step `equality` through the modulus. |
| `(b1-mod-expt-squared-power ring integral natural)` | The reduced-square exponentiation equality, with the resulting Library. The arguments after `ring` are the base integrality and exponent naturality Steps. |
| `(b1-mod-expt-shift-natural lib integral positive-index)` | A list of the naturality and floor equality Steps for the shifted index, with the resulting Library. The arguments after `lib` are its integrality and positivity Steps. |
| `(b1-mod-expt-accumulator-invariant lib)` | The name of the accumulator invariant fact, with the resulting Library. |
| `(b1-mod-expt-mod-expt-fast lib formula)` | The proof Step for the translated implication term `formula` relating the fast and ordinary exponentiations, with the resulting Library. |

The prover symbols are `*b1-mod-expt-a*`, `*b1-mod-expt-i*`,
`*b1-mod-expt-n*`, `*b1-mod-expt-acc*`, `*b1-mod-expt-fast*`,
`*b1-mod-expt-wrapper*`, `*b1-mod-expt-mod-expt*` and
`*b1-mod-expt-oddp*`.
