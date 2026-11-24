# Completed operations

In these calls, `lib` is a Library, a term is prover data, and a Step is a
proof step as specified in `prover/sig/`. The functions return a failure in
place of the result if proof construction fails. A result that is a
Library contains the new lemmas in the order of their addition.

`*t2-completed-operations-lognot*` and `*t2-completed-operations-logorc1*`
are the Common Lisp symbols `LOGNOT` and `LOGORC1` in prover data.
`*t2-completed-operations-logand*`, `*t2-completed-operations-logior*`,
`*t2-completed-operations-logeqv*`, and `*t2-completed-operations-logxor*`
are the ACL2 symbols for the corresponding binary bit operations.

| ACL2 call | Arguments and result |
|---|---|
| `(t2-completed-operations-zero-mod lib floor-zero)` | Given equality Step `floor-zero` for the zero floor, return the remainder equality Step. |
| `(t2-completed-operations-rounding-defaults lib)` | Return the Library with completion lemmas for floor and remainder. |
| `(t2-completed-operations-lognot-zero lib value missing)` | Given term `value` and Step `missing` denying its integrality, return a Step equating its bitwise negation to that of zero. |
| `(t2-completed-operations-logand-default lib first second position missing)` | Given operand terms `first` and `second`, their one-based position `position`, and Step `missing` denying integrality at that position, return a Step for their bitwise conjunction. |
| `(t2-completed-operations-xor-expansion lib arguments)` | Given the ordered operand term list `arguments`, return an equality Step expanding the bitwise exclusive disjunction. |
| `(t2-completed-operations-bit-defaults lib)` | Return the Library with completion lemmas for bitwise conjunction, disjunction, and exclusive disjunction. |
| `(t2-completed-operations-build lib)` | Return the Library with the rounding and bit operation completion lemmas. |
