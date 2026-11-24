# DO$ congruence

`p` is the Library used for the book tactics. Terms and Steps follow
`prover/sig/proof.md`.

`(h4-do-loop-do-congruence p formula)` takes a congruence formula for
`DO$`. It returns `(cons step p)` with a Step proving the formula and
the Library holding the auxiliary lemmas and definitions. It can return
a failure in place of the pair.
