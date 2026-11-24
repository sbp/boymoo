# Witnesses

Witness construction tries candidate function definitions in order and
returns the first assignments that discharge all constraints. The
witness symbols are in constrained-function order, and the proof Steps
are in constraint order.

The state-returning recipes pair the result with their Library. They
let the statement generator retain auxiliary definitions and proofs
when it proceeds after an unproved obligation. The evaluator recipe
carries Library updates from its completed evaluator calls.
