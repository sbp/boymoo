# Bits

Terms, symbols and Steps use the forms in `prover/sig/proof.md`. A Library
has the form in `prover/sig/library.md`. A result written `(cons value lib)`
carries the Library after any auxiliary lemmas have been added. On a
failure, that value is the entire result.

`*b1-bits-evenp*` is the Common Lisp `EVENP` symbol.
`*b1-bits-two*` is the term quoting 2.

| Call | Result | Failure |
|---|---|---|
| `(b1-bits-low-bit n)` | The conditional term for the low bit of term `n`, using `EVENP`. | None. |
| `(b1-bits-join-bits q bit)` | The term for twice term `q` plus term `bit`. | None. |
| `(b1-bits-even-equation lib n)` | A Step equating `EVENP` of term `n` to the integer test of its half. | A failure from proof construction. |
| `(b1-bits-half-interval lib integral)` | `(cons (list bounds rational) lib)`, given the integer Step for the dividend. `bounds` lists the integrality, lower bound and upper bound Steps in that order for the floor by two. `rational` is the rationality Step for the half. | A failure from proof construction. |
| `(b1-bits-displaced-floor lib bounds rational integral displacement amount)` | `(cons step lib)` equating the floor to the integer part. `bounds` is the ordered list of interval Steps, `rational` is a rationality Step, `integral` is the integer part's Step, `displacement` equates the rational value to the part plus `amount`, and `amount` is the term quoting zero or one half. | A failure for a mismatched displaced term or during proof construction. |
| `(b1-bits-double-half lib n numeric)` | A Step equating twice the half of term `n` to `n`, given its numeric Step. | A failure from proof construction. |
| `(b1-bits-decomposition lib integral)` | `(cons step lib)` for the high and low bit decomposition of the term in integer Step `integral`. | A failure from proof construction. |
| `(b1-bits-bit-pair lib integral bit)` | `(cons (list floor even) lib)` for the high half and evenness of twice the term in integer Step `integral` plus the constant term `bit`. The result Steps are in that order. | A failure from proof construction. |
| `(b1-bits-constant-bit-pair lib high low)` | `(cons (list floor even) lib)` for the high half and evenness of the normalized term twice `high` plus `low`, given two quoted integer terms. The result Steps are in that order. | A failure from proof construction. |
