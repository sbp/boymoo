# Bit types

`lib` is the B1 Library. Terms, symbols, and Steps have the forms in
`prover/sig/proof.md`. Each function can return a failure in place of its result.
A pair with an updated Library uses `(cons value lib)`. Step lists retain
the order in which they are supplied. A missing prior type is `nil`.

| ACL2 call | Arguments and result |
|---|---|
| `(b1-bit-types-integer-fix lib value)` | An integer Step for the fixing term `value`. |
| `(b1-bit-types-typed-bit-is-natural lib bit)` | A natural Step for the subject of the bit Step `bit`. |
| `(b1-bit-types-prior-type lib value)` | The instantiated type Step for term `value` from a named fact, or `nil` when the fact is absent. |
| `(b1-bit-types-floor-integer lib floor x-type y-type)` | An integer Step for term `floor`, paired with the updated Library. The last two arguments are its operands' integer Steps. |
| `(b1-bit-types-mod-two-equation lib integral)` | An equality Step for the remainder modulo two of the subject of integer Step `integral`, paired with the updated Library. |
| `(b1-bit-types-positive-power-of-two lib exponent natural)` | The list of integer and positive Steps for two raised to term `exponent`, in that order, paired with the updated Library. `natural` is the exponent's natural Step. |
| `(b1-bit-types-exponent-types n lib term)` | The list of integer and positive Steps for power term `term`, in that order, paired with the updated Library. |
| `(b1-bit-types-and-integer n lib expression)` | An integer Step for binary conjunction term `expression`, paired with the updated Library. |
| `(b1-bit-types-numeric-type n lib predicate value evidence)` | A type Step for the `predicate` symbol on term `value`, paired with the updated Library. `evidence` is an ordered list of Steps. |
| `(b1-bit-types-reverse-is-natural n lib call initial)` | A natural Step for reversal term `call`, paired with the updated Library. `initial` is the accumulator's natural Step. |
| `(b1-bit-types-bit-operation-type lib formula)` | A Step for the bit-operation type formula, paired with the updated Library. |

`n` is natural-number fuel. Pass `1000000` at the start of a recursive
search. Type proofs may add lemmas in the order in which they are needed.

The symbol constants are `*b1-bit-types-expt*`, `*b1-bit-types-lognot*`,
`*b1-bit-types-fix*`, `*b1-bit-types-bfix*`, `*b1-bit-types-logand*`,
`*b1-bit-types-logior*`, `*b1-bit-types-imod*`, `*b1-bit-types-expt2*`,
`*b1-bit-types-logcar*`, `*b1-bit-types-logcons*`, `*b1-bit-types-logrev1*`
and `*b1-bit-types-builtin-nfix*`. `*b1-bit-types-typed-operations*` maps
operation symbols to type-fact symbols in the order of their entries.
