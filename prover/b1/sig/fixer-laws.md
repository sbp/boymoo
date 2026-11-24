# Value fixer laws

`lib` is a Library as specified in `prover/sig/library.md`. Terms and Steps
have the forms in `prover/sig/proof.md`. Each function returns a Step or
a failure value `(:failure kind message)` from reading the arguments or
constructing the proof.

| ACL2 call | Arguments and result |
|---|---|
| `(b1-fixer-laws-bit-fix-identity lib formula)` | Prove the implication that a bit fixer leaves a recognized bit unchanged. |
| `(b1-fixer-laws-maybe-recognizer lib formula)` | Prove the implication or conditional equation for an optional-value recognizer. |
| `(b1-fixer-laws-equality-equivalence lib formula)` | Prove Boolean typing, reflexivity, symmetry and transitivity for equality of fixed values. |
| `(b1-fixer-laws-fixed-character-code lib fixed)` | For a unary character fixer call `fixed`, equate the character code of its argument to the character code of the fixed value. |
| `(b1-fixer-laws-fixed-string-characters lib fixed)` | For a unary string fixer call `fixed`, equate the character list of its argument to the character list of the fixed value. |
| `(b1-fixer-laws-fixed-congruence lib formula)` | Prove the implication from equivalence of fixed values to the given equality. |

`*b1-fixer-laws-bitp*`, `*b1-fixer-laws-posp*` and
`*b1-fixer-laws-booleanp*` are the respective ACL2 symbol terms.
`*b1-fixer-laws-char-code*` and `*b1-fixer-laws-code-char*` are Common Lisp
symbol terms. `*b1-fixer-laws-list*` is the quoted Common Lisp `LIST` term.
