# Ordinal order proof signatures

`lib` is a library and `step` is a proof step. Both functions can return a failure in place of their result.

| ACL2 call | Arguments and result |
|---|---|
| `(ordinal-proofs-ordinal-zero-lemmas lib)` | Adds the lemmas about the order of zero and returns the resulting library. |
| `(ordinal-proofs-positive-ordinal lib comparison left-ord right-ord)` | `comparison` proves a strict ordinal comparison. `left-ord` and `right-ord` prove the respective operands are ordinals. Returns `(cons step lib)` with a proof that the right operand is above zero. |
