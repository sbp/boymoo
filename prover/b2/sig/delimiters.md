# Delimiter and lookup result types

Each function takes a Library `lib`. Libraries, terms, and Steps have the
forms given in `prover/sig/library.md` and
`prover/sig/proof.md`. `formula` is the theorem term. Boolean arguments are
`t` and `nil`.

| Call | Result |
|---|---|
| `(b2-delimiters-delimiter-type lib formula after)` | Proof of the pre-delimiter type when `after` is `nil`, or of the post-delimiter implication when it is `t`. |
| `(b2-delimiters-property-lookup lib formula boolean)` | Proof of the world property lookup's symbol-list type or, when `boolean` is `t`, its Boolean type. |
| `(b2-delimiters-delimiter-theorem lib name formula)` | Proof using the recipe selected by theorem symbol `name`. |

The theorem symbols are `*b2-delimiters-pre*`, `*b2-delimiters-post*`,
`*b2-delimiters-return-values*`, and `*b2-delimiters-logic-mode*`.
`*b2-delimiters-delimiter-types*` lists those symbols in symbol-name order
for membership tests.

The result of `b2-delimiters-delimiter-type` and
`b2-delimiters-delimiter-theorem` is `(cons step lib)`. The resulting Library
contains any auxiliary projection lemmas. `b2-delimiters-property-lookup`
returns its Step directly. A failure is the entire result in all three calls.
