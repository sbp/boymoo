# Descent proofs for book definitions

A measure map assigns a measure term to each recursive definition. The
termination tactic tries measures from the aids before enumerating
measures from the recursive call arguments.

The set-selector and termination `-with-library` functions pair their
results with the Library reached during the proof attempt. A later
tactic can use auxiliary entries registered by that attempt.
