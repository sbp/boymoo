# Strict lexicographic comparison

`lib` is a Library as specified in `prover/sig/library.md`. A term and a Step have the forms in `prover/sig/proof.md`. Evidence is a list of Steps in the supplied order. The functions keep the Library unchanged. A failure is the entire result.

| ACL2 call | Result | Failure |
|---|---|---|
| `(b2-strict-lexicographic-strict-lexorder-equivalence lib formula)` | Step for the equality of the fast and strict lexicographic comparisons in the term `formula`. | Failure from reading the formula or constructing the proof. |
| `(b2-strict-lexicographic-signs lib test)` | List of the Steps for the true and false branches of term `test`, in that order. | Failure from proof construction. |
| `(b2-strict-lexicographic-reverse-order lib a b)` | Step equating the strict comparison of terms `a` and `b` with the negation of their reverse order. | Failure from proof construction. |
| `(b2-strict-lexicographic-strict-atom-cases lib fast reverse dual base)` | Step equating the fast comparison term `fast` with the negation of term `reverse` in the atomic cases. `dual` is the reverse-order Step and `base` is the evidence that both arguments are atomic. | Failure from reading the terms or constructing the proof. |

The symbol constants are `*b2-strict-lexicographic-char-code*`, `*b2-strict-lexicographic-realpart*`, `*b2-strict-lexicographic-imagpart*`, `*b2-strict-lexicographic-string-less*`, and `*b2-strict-lexicographic-string-weak*`.
