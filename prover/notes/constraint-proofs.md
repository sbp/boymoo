# Constraint witnesses

`constraint-proofs-construct-witnesses` considers definition options in
Cartesian product order and returns the first witness with proofs of
its constraints. Each attempted candidate can add auxiliary entries.
When a candidate is unproved, the tactic rolls back its additions
before trying the next one.
