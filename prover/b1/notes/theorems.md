# Theorem recipes

The named theorem dispatch maps obligation labels to recipe symbols.
Recipes can use the context's FactIndex to obtain evidence from earlier
facts. The signature in `prover/b1/sig/theorems.md` describes the dispatch
and the Library returned with a proof.

`A-IN-ACL2-PKG` requires the imports of a hidden package at a symbolic
argument. The statement generator records it as unproved when it lacks
an admitted fact for the formula.
