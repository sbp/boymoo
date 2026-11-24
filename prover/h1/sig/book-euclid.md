# Euclidean greatest common divisor

`proof` is an H1 proof world. Terms and Steps have the forms in `prover/sig/proof.md`. A failure replaces the entire result.

`*h1-book-euclid-gcd*`, `*h1-book-euclid-multiplier1*` and `*h1-book-euclid-multiplier2*` are the ACL2 symbol data for `NONNEG-INT-GCD`, `NONNEG-INT-GCD-MULTIPLIER1` and `NONNEG-INT-GCD-MULTIPLIER2`.

| Call | Result |
|---|---|
| `(h1-book-euclid-euclidean-induction proof formula base recursive)` | Step proving `formula` by Euclidean induction. `base` and `recursive` describe the branch functions with their closed-over arguments. A GCD sign branch uses `(:gcd-positive equation either-positive)` for `base` and `(:gcd-positive equation)` for `recursive`. A linear combination branch uses `(:bezout expansions polynomial typed)` for `base` and `(:bezout expansions polynomial typed quotient remainder)` for `recursive`. The lists `expansions` and `typed` are used in their supplied order. |
| `(h1-book-euclid-gcd-positive proof)` | Step proving that the greatest common divisor is positive under the positivity premise. |
| `(h1-book-euclid-install-gcd proof)` | Proof world with the positivity theorem recorded. |
| `(h1-book-euclid-bezout proof)` | Step proving integrality of the multipliers and their linear combination identity. |
| `(h1-book-euclid-install-bezout proof)` | Proof world with the linear combination lemmas in order. |

Each function can return a failure from a proof operation.
