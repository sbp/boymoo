# Quotient descent

The quotient tactics carry the resulting library because type proofs
can introduce auxiliary lemmas. The descent variant with Rulers also
returns the dividend hypotheses it established.

Radix induction prepares an instance, requests its branch proofs and
then assembles the induction. The candidate calls are traversed in
order. The continuation after an unsuccessful candidate preserves
the position of that candidate in the traversal.
