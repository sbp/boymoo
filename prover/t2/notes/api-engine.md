# Proof context and generation

The default measures associate function names with measures and
relations in measure event order. The engine merges these measures with
the supplied aids when an obligation concerns termination.

`t2-api-engine-obligation` reads the fields needed by the proof tactic.
`t2-api-engine-proof-text-parts` selects its helper entries and separates
the main proof source. The session interface uses both operations.
