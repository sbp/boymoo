# Theorem recipes

A recipe recognizes a theorem form and builds its proof using the
definitions and facts already admitted. Call substitutions are
traversed in order. Arithmetic recipes can request helper entries and
retain the resulting prover between requests.

If the sign and type facts are absent, the basic type recipe calls
`h1-recursion-build` before constructing its result.
