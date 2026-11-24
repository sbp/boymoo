# Type fixer invariance

`lib` is a Library as specified in `library.md`. `call` is a term applying a primitive, `fixed` is the term that fixes its first argument, and `fitted` applies the primitive to the fixed argument. `branch` is the conditional right side of the Step `equation`.

| ACL2 call | Result |
|---|---|
| `(fixer-proofs-fixer-invariance lib call fixed)` | `(cons step lib)`, where `step` proves invariance or is `nil` if the tactic found no proof. The Library can gain the invariance lemma. |
| `(fixer-proofs-fixer-invariance-select holds lib branch equation fitted)` | A Step proving the equality for the selected conditional branch. `holds` is `t` for the true branch and `nil` for the false branch. |

Both functions can return a failure. The constants are `*fixer-proofs-char-code*`, `*fixer-proofs-coerce*`, and `*fixer-proofs-list*`. They are the `CHAR-CODE` and `COERCE` symbols and the quoted `LIST` symbol.

`fixer-invariance` puts a failure in the Step position of its result.
