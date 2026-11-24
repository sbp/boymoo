# Subtraction and count descent

`lib` is a SliceLibrary or BookLibrary, in the Library form from
`prover/sig/library.md`. Terms and Steps use the forms in `prover/sig/proof.md`.
Each call can return a failure in place of its listed result. A result written
`(cons value lib)` contains the value and the Library after any additions.

| Function | Arguments in order | Result |
|---|---|---|
| `subtraction-positive-nfix-input` | `lib`, `value` (term), `nonzero` (Step for nonzero `NFIX` result) | `(cons (list int-proof pos-proof) lib)` |
| `subtraction-prove-count-identity` | `lib`, `value` (term), `int-proof`, `bound` (Steps for integrality and nonnegativity) | `(cons step lib)` proving equality of the count and `value` |
| `subtraction-count-identity` | `lib`, `value` (term), `int-proof`, `bound` (Steps for integrality and nonnegativity) | `(cons step lib)` proving the same equality through a named lemma |
| `subtraction-subtraction-decrease` | `lib`, `goal` (count comparison), `rulers` (Rulers object) | `(cons step lib)` proving the descent, or `(cons nil lib)` when the tactic does not apply |

The term constants are `*subtraction-nfix*`, `*subtraction-ifix*`,
`*subtraction-integer-abs*`, and `*subtraction-numeric-equal*`.

`subtraction-subtraction-decrease-with-rulers` takes the same three
arguments as `subtraction-subtraction-decrease`. It returns
`(cons (list step rulers) lib)`, with the resulting Rulers and with
`nil` in the step position when the tactic does not apply. A failure can
appear in place of the pair.
