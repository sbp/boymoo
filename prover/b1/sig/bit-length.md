# Bit length

`*b1-bit-length-length*`, `*b1-bit-length-logcdr*`, and
`*b1-bit-length-ifloor*` are the symbols for `INTEGER-LENGTH`,
`LOGCDR$INLINE`, and `IFLOOR$INLINE`.

`lib` is a Library as in `prover/sig/library.md`. Terms and Steps use the
forms in `prover/sig/proof.md`. Each call can return a failure in place of
the listed result. A pair `(value . lib)` carries the Library with any
lemmas added during the call.

| ACL2 call | Arguments and result |
|---|---|
| `(b1-bit-length-open-length lib term)` | Returns a list of the zero test, the minus-one test, and the three Steps for the zero, minus-one, and recursive branches of the integer length of `term`, in that order. |
| `(b1-bit-length-natural-bit-length lib term)` | Returns `(step . lib)` proving that the integer length of `term` is natural. |
| `(b1-bit-length-fixed-integer-when-zero lib term zero)` | `zero` proves `(ZIP term)`. Returns a Step proving that `(IFIX term)` is zero. |
| `(b1-bit-length-high-bits-at-fixed-point lib term fixed)` | `fixed` equates `(IFIX term)` to a fixed point of signed halving. Returns the length equation for the high bits of `term`. |
| `(b1-bit-length-length-halving-cases lib term replies)` | Returns `(step . lib)` joining the consequences for the zero, minus-one, and recursive branches, or a request for a consequence in the value position. |
| `(b1-bit-length-bit-length-sum-ordinal lib measure)` | `measure` is a sum of two integer lengths. Returns `(step . lib)` proving that the sum is an ordinal. |
| `(b1-bit-length-paired-bit-length-descent lib goal stop-test)` | `goal` is the ordinal comparison of the child and parent sums of lengths. `stop-test` is the term testing whether both lengths are zero. Returns `(step . lib)` proving the descent outside that case. |
| `(b1-bit-length-integer-non-nil lib integral)` | `integral` proves `(INTEGERP term)`. Returns a Step proving `term`. |
| `(b1-bit-length-mismatch-is-integer lib formula)` | `formula` states that a non-NIL mismatch result is integer. Returns `(step . lib)` proving the formula. |

Start `length-halving-cases` with `nil` replies. Its request has the
form `(:b1-bit-length-case parent child decreasing-p)`. The two Steps
give the equations for the input length and the high-bit length in that
branch. Pass them and the Boolean to the consequence, using the Library
paired with the request. To answer it, append the consequence's
`(step . lib)` pair to the replies and call again with the original
Library and term. Pass a consequence's failure as the entire reply.
