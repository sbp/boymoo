# List recognition and preservation

The Library, term and Step arguments have the forms in the shared signatures.
Every call can return a failure. Optional list arguments use `nil` for
omission. Names, definitions, calls and evidence retain their order.

| Call | Result |
|---|---|
| `(h3-lists-cdr-induction lib formula variable names definitions calls)` | Step proving the formula by CDR induction on the variable term. Names are rule names, definitions are function names, and calls are terms. |
| `(h3-lists-cdr-induction-prove-case evidence lib definitions calls names formula)` | Step for an induction case under the ordered evidence Steps. |
| `(h3-lists-recognizer-implication lib formula)` | Step for the recognizer implication formula. |
| `(h3-lists-list-tail-rule lib predicate)` | `(cons name lib)` with the auxiliary CDR rule for the predicate symbol in the Library. |
| `(h3-lists-association-cdr lib formula)` | Step for the recognizer of the tail of the association. |
| `(h3-lists-eqlable-nth lib formula)` | Step for the recognizer of an indexed entry in a list. |
| `(h3-lists-eqlable-nth-prove-case evidence lib calls formula)` | Step for the indexed-entry induction case under the ordered evidence Steps. |
| `(h3-lists-printed-phrase lib formula)` | `(cons step lib)` for the printed phrase's list recognizer, with the auxiliary lemmas in the Library. |
| `(h3-lists-true-list-cons lib)` | `(cons name lib)` with the true-list recognizer rule for `CONS` in the Library. |
| `(h3-lists-explode-atom lib formula)` | `(cons step lib)` for the exploded atom's list recognizer, with the auxiliary lemmas in the Library. |
| `(h3-lists-resize-list lib formula)` | `(cons step lib)` for equivalence of the resize implementations, with the auxiliary lemmas in the Library. |
| `(h3-lists-resize-list-prove-case evidence lib executable logical rules formula)` | Step for the resize induction case given the evidence Steps, both implementation terms and a Rules object. |

A returned name is a symbol term. The symbol constants are
`*h3-lists-atom*`, `*h3-lists-endp*`, `*h3-lists-eq*`,
`*h3-lists-null*`, `*h3-lists-nth*`, `*h3-lists-posp*`,
`*h3-lists-zp*`, `*h3-lists-true-listp*`, `*h3-lists-symbol-listp*`,
`*h3-lists-eqlablep*` and `*h3-lists-eqlable-listp*`.
The constants `*h3-lists-list-definitions*` and `*h3-lists-selectors*`
list the definitions and selector rules in source order.
