# Remainder proofs

`*remainder-proofs-mod*` is the prover symbol for `MOD`.
`*remainder-proofs-remainder-bounds*` is the lemma name string.

The `lib` argument is a Library. A term and a Step have the forms in
`prover/sig/proof.md`. Both functions can return a failure in place of the
listed result.

| ACL2 call | Arguments and result |
|---|---|
| `(remainder-proofs-remainder-lemma lib)` | Returns the Library with the remainder bounds lemma. |
| `(remainder-proofs-remainder-premise lib goal known)` | Given the goal term and an alist of known terms to Steps, returns `(step . lib)` with the resulting Library. The Step is `nil` when the bounds do not prove the goal. |
