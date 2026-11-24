# Tactics and evidence

The search uses claim and rewrite indexes, a context of signed tests and
derived evidence, and a budget for proof steps and case splits.
Schemas use `:none` for an absent argument head. Variable sets use the
serialization supplied by `h1-tactics-variable-text` to determine their
order.

Formula registration updates the facts, schemas, and exact theorem
index together. Definition openings and the case limit belong to the
current proof attempt.
