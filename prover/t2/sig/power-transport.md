# Power transport

The Library, terms, and Steps have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. Each function can return a failure in place of its
listed result. A function that adds lemmas returns the updated Library,
with entries in the order in which the function adds them.

| ACL2 call | Result |
|---|---|
| `(t2-power-transport-inverse-factors lib)` | Library with the left and right rational reciprocal cancellations, in that order. |
| `(t2-power-transport-zero-base-negation lib integral base-zero)` | Step equating the power of `X` at exponent `-Y` to the power of the reciprocal of `X` at exponent `Y`. The two Steps establish that `Y` is an integer and that the numeric fix of `X` is zero. |
| `(t2-power-transport-power-reciprocals lib)` | Library with the reversed reciprocal base identity, transport of exponent negation to the base, and the minus-one and negative-factor exponent identities. |
| `(t2-power-transport-rational-reconstruction lib)` | Library with the reconstruction of a rational from its numerator and denominator. |
| `(t2-power-transport-power-sum lib)` | Library with the power sum identity for integer exponents whose sum is nonzero. |
| `(t2-power-transport-numeric-completion lib)` | Library with the nonnumber completions for division and exponentiation, in that order. |
| `(t2-power-transport-build lib)` | Library extended by inverse factors, power reciprocals, rational reconstruction, power sum, and numeric completion, in that order. |
