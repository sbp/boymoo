# Recognizers and constructors for translated terms

`lib` is a Library. `formula` and `argument` are terms. `name` is a theorem
symbol. Libraries, terms, and Steps have the forms in `prover/sig/library.md`
and `prover/sig/proof.md`. All calls may return a failure in place of their
listed result. In `(cons step lib)` results, the Library includes any
auxiliary lemma added during proof construction.

| Call | Result |
|---|---|
| `(b2-pseudo-terms-definition-equation lib formula)` | Proof Step using the definition of the call in the formula. |
| `(b2-pseudo-terms-list-boolean lib argument)` | `(cons step lib)` for the Boolean type of the pseudo-term-list predicate. |
| `(b2-pseudo-terms-pterm-opener lib formula)` | `(cons step lib)` for the pseudo-term recognizer opener. |
| `(b2-pseudo-terms-term-tail lib formula)` | Proof Step for the tail of a nonquoted pseudo-term. |
| `(b2-pseudo-terms-list-selector lib formula)` | Proof Step for the head or tail of a pseudo-term list. |
| `(b2-pseudo-terms-cadr-lookup lib formula)` | Proof Step for the second element of a pseudo-term list. |
| `(b2-pseudo-terms-alist-lookup lib formula)` | Proof Step for the pseudo-term returned by a substitution or value lookup. |
| `(b2-pseudo-terms-typed-options lib formula)` | Proof Step for the type of the option-entry tail. |
| `(b2-pseudo-terms-preserve-pseudo lib name formula)` | `(cons step lib)` using the preservation recipe selected by `name`. |

The symbol constants are `*b2-pseudo-terms-booleanp*`,
`*b2-pseudo-terms-subst*`, `*b2-pseudo-terms-vals*`,
`*b2-pseudo-terms-list-cdr*`, and `*b2-pseudo-terms-term-car*`.
`*b2-pseudo-terms-pseudo-theorems*` lists the supported theorem symbols
for membership tests.
