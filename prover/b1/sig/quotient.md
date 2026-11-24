# Integer quotient and right shift

The symbol constants are `*b1-quotient-ash*`, `*b1-quotient-expt*`,
`*b1-quotient-floor*`, `*b1-quotient-niq*`, `*b1-quotient-ifix*`,
`*b1-quotient-zip*`, `*b1-quotient-abs*`, and
`*b1-quotient-numeric-eq*`. They denote `ASH`, `EXPT`, `FLOOR`,
`NONNEGATIVE-INTEGER-QUOTIENT`, `IFIX`, `ZIP`, `INTEGER-ABS`, and `=`.

`lib` is the Library from `prover/sig/library.md`. Proof arguments and proof
results are Steps from `prover/sig/proof.md`. A result paired with a Library
uses `(cons value lib)`. The Library retains entries and facts in insertion
order. Any failure replaces the entire result.

| Call | Arguments after `lib` | Result | Failure |
|---|---|---|---|
| `(b1-quotient-natural-from-positive lib term integer-proof positive-proof)` | Term, its integrality proof, and its strict positivity proof | Proof that `term` is natural | Can return a failure |
| `(b1-quotient-quotient-bounds lib)` | None | Pair of the lemma name and the Library containing the lemma | Can return a failure |
| `(b1-quotient-count-natural lib natural)` | Proof of naturalness of the argument | Equality reducing `ACL2-COUNT` of that argument | Can return a failure |
| `(b1-quotient-count-integer lib integer-p sign)` | Integrality and sign proofs for the argument | Equality reducing `ACL2-COUNT` of that argument | Can return a failure |
| `(b1-quotient-quotient-less lib int-n int-d pos-d pos-n int-i strict)` | Proofs that `n`, `d`, and `i` are integers, that `d` and `n` are positive, and that `n < d*i`, supplied in the order shown | Pair of `(less nat-q)` and the resulting Library. `less` proves the quotient less than `i`, and `nat-q` proves it natural. | Can return a failure |
| `(b1-quotient-floor-half-bound lib i int-i pos-i)` | Term `i` with proofs of integrality and strict positivity | Pair of `(less natural)` and the resulting Library. The two Steps prove `floor(i/2) < i` and naturalness of `floor(i/2)`. | Can return a failure |
| `(b1-quotient-shift-descent lib goal)` | Right shift descent claim | Pair of the instantiated descent Step and the resulting Library | Can return a failure |
