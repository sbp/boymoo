# Alist agreement proofs

`p` is the H4 Tactics library. A formula is a prover term and a Step has the
form in `prover/sig/proof.md`.

| ACL2 call | Result | Failure |
|---|---|---|

The constants `*h4-book-agreement-lookup*`, `*h4-book-agreement-get*`,
`*h4-book-agreement-member*`, `*h4-book-agreement-agree*`,
`*h4-book-agreement-disagree*`, `*h4-book-agreement-subset*`,
`*h4-book-agreement-subset-witness*`, `*h4-book-agreement-equiv*`,
`*h4-book-agreement-bad-guy*`, `*h4-book-agreement-iff*` and
`*h4-book-agreement-hons-equal*` are the corresponding ACL2 symbol terms.

`(h4-book-agreement-agreement-proof-with-choices p formula choices)` has
the same result and receives the world’s separate choice table. `choices`
is the insertion-ordered association list specified in `book-choice.md`.
Use this entry point when the world has choices. `agreement-proof` uses
an empty choice table.
