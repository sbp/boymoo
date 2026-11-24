# Signed halving and bitwise conjunction

`lib` is a Library, `formula` and `argument` are terms, and `numeric` is a
Step proving that `argument` is an ACL2 number. Terms, Steps and Libraries
have the forms in `prover/sig/proof.md` and `prover/sig/library.md`.

The constants are `*b1-bitwise-logand*` for `BINARY-LOGAND`,
`*b1-bitwise-two*` for quoted 2, and `*b1-bitwise-half*` for quoted 1/2.

| Call | Result |
|---|---|
| `(b1-bitwise-twice lib argument numeric)` | Step equating the sum of `argument` with itself to the product of 2 and `argument`. |
| `(b1-bitwise-floor-half-descent lib)` | `(cons name lib)` with the name of the signed halving decrease fact and the resulting Library. |
| `(b1-bitwise-logand-commutative lib formula)` | `(cons step lib)` with the proof of the commutativity formula and the resulting Library. |
| `(b1-bitwise-interchange-logand lib formula)` | Step proving interchange of the first two factors of nested bitwise conjunctions. |

Each call may return a failure as its entire result. The commutativity recipe
visits each true branch before the corresponding false branch. Its
induction substitution binds the first operand before the second.
