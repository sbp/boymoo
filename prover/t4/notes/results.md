# Result properties

The result tactics prove properties of values returned by functions.
They request knowledge, fact proofs, equations, proof search and
arithmetic initialization from the tactic context. The query calls
take the ordered replies as their last argument. A solve request
includes the goal, tests, extra premises and depth.

The projection tactic retains the Library when its proof attempt
fails. Its Library and request forms are in `prover/t4/sig/results.md`.
