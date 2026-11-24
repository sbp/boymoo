# Symbolic application

The application reducer uses the Proof kind when selecting its constant rules. For a WarrantProof, it computes `SYMBOLP`, `CAR`, and `CDR` on quoted arguments, then uses the general Proof rules for other terms. The guarded application kinds add a rule for a symbol test on a cons and a branch rule for a non-Boolean quoted test.

Sets of function symbols are lists ordered by the ACL2 text of their members. The signatures give the fields of the application record and the order of the argument projections.
