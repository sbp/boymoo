# Structural proof state

Reducing a term can install auxiliary lemmas and add derived facts.
The Reduction carries those changes while the tactic normalizes the
term and chooses case tests. Its paired results and
`t2-structural-proof-reduction-reply` carry the state to the next tactic.
