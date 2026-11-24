# Numeric completion and complex arithmetic

The Library, term and Step arguments have the forms in the shared signatures.
Every call can return a failure in place of its result.

| Call | Result |
|---|---|
| `(h3-numeric-complex-zero lib term)` | Step reducing a complex constructor with zero imaginary part. |
| `(h3-numeric-real-and-imaginary lib value)` | Two Steps proving rationality of the real and imaginary parts of term `value`, in that order. |
| `(h3-numeric-rational-components lib rational)` | Three Steps for a rational value given its rationality Step. They prove that its real part equals the value, its imaginary part equals zero, and it is an ACL2 number, in that order. |
| `(h3-numeric-comparison-default lib formula)` | Step for the comparison formula, with an absent number treated as zero. |
| `(h3-numeric-rational-sum lib a b)` | Step proving a rational sum given the two rationality Steps in summand order. |
| `(h3-numeric-decompose lib value)` | Step equating the complex constructor on the two parts of term `value` with its fixed value. |
| `(h3-numeric-expand-complex lib a b)` | Step expanding a complex constructor given the rationality Steps for its real and imaginary inputs. |
| `(h3-numeric-addition-of-complex-parts lib formula)` | `(cons step lib)` for the addition formula, with the auxiliary right-zero lemma added to the Library. |
| `(h3-numeric-part-of-sum lib formula)` | Step equating the real or imaginary part of a sum with the sum of the corresponding parts. |

The symbol constants `*h3-numeric-complex*`, `*h3-numeric-real*`,
`*h3-numeric-imaginary*`, `*h3-numeric-fix*` and
`*h3-numeric-realfix*` denote `COMPLEX`, `REALPART`, `IMAGPART`,
`FIX` and `REALFIX`, respectively.
