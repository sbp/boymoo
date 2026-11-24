# Logical state updates

The Library, term and Step arguments have the forms in the shared signatures.
Every call can return a failure in place of its result.

| Call | Result |
|---|---|
| `(h3-state-true-list-not-string lib)` | `(cons name lib)` for the auxiliary lemma that a true list cannot be a string. The Library contains the lemma. |
| `(h3-state-true-list-length lib)` | `(cons name lib)` for the auxiliary equality of `LENGTH` and `LEN` on true lists. The Library contains the lemma and its prerequisites. |
| `(h3-state-state-update lib formula)` | `(cons step lib)` for the state update formula, with its auxiliary lemmas in the Library. |

A lemma name is a symbol term. The symbol constants are
`*h3-state-true-listp*`, `*h3-state-state-p1*`, `*h3-state-stringp*`,
`*h3-state-length*` and `*h3-state-max*`. The definition names in
`*h3-state-state-fields*` are in source order.
