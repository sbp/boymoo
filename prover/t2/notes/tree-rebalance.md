# Tree rebalancing

The structural reductions in `simplify-build`, `short-prefix`, and
`proper-length` can install auxiliary lemmas. Their results carry the
updated Library. `t2-tree-rebalance-prove-attempt` also carries it when
the proof ends with `unproved`, so the next tactic can use those lemmas.
