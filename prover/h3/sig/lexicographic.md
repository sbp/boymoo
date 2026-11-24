# Lexicographic order

The Library, term and Step arguments have the forms in the shared signatures.
A replacement is a pair represented as a two-element list, with a substitution
association list followed by a built-in clause number. The list orders variables
in the order supplied to the induction.

| Call | Result |
|---|---|
| `(h3-lexicographic-reconstruct-cons lib)` | `(cons name lib)` with the congruence lemma added to the Library. |
| `(h3-lexicographic-lexorder lib name formula)` | `(cons step lib)` for the named lexicographic law. The Library includes the auxiliary congruence lemma for antisymmetry. `name` is a string. |
| `(h3-lexicographic-lexorder-prove-case evidence lib names calls property-name formula)` | A proof Step for the formula under the ordered list of evidence Steps. The names and calls are ordered lists. The property name is the string after removing the `LEXORDER-` prefix. |

All calls can return a failure in place of the listed result. The name returned
by the constructor is a symbol term. The laws are `REFLEXIVE`,
`ANTI-SYMMETRIC`, `TRANSITIVE` and `TOTAL`. The `LEXORDER` symbol
constant is `*h3-lexicographic-lex*`.
