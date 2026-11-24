# Proof-producing rewriting

The claims alist accepts `:b1-rule` records. Its key distinguishes an
absent compound first argument, represented by `:none`, from an empty
compound head, represented by `nil`. Exact candidates precede general
candidates, and each group is searched from newest to oldest.

The normalization callbacks carry the current Library and the term
being reduced. A branch result carries the test to split and the
Library available at that point.

`b1-logic-proof-not-nil` uses the ground Step for quoted NIL when
the supplied Proof has the premises used to construct that Step.
