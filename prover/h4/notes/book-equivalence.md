# Equivalence rewriting

An equivalence proof starts a lookup scope for its own premises.
Congruence lifts start fresh scopes, so distinct sets of evidence use
their own lookup histories even when they contain equal Steps.
Pending rewrite candidates are ordered by term size and then by
insertion number.
