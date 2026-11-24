# Termination measures

Measure search tries the supplied aids, selector measures, and measures
based on individual formals, in that order. It keeps track of attempted
measure lists and carries the Library into the next plan.
`b1-measures-termination-with-library` returns the resulting Library
with the proof or failure. The signature is in `prover/b1/sig/measures.md`.
