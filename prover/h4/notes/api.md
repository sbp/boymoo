# Proof preparation

Core support uses `h4-terms-tactics-build` to construct the library
lemmas with H4 conjunction and implication rules. The session installs
core, pointwise and warrant support where their proofs require it.

`h4-api-proof-draft` selects printing and ordinal support from the
target's form. The proof writer keeps the auxiliary entries needed by
the selected proof and renames them in dependency order.
