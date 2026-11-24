# Logic and Evidence

`t3-logic-libraryproofs-for-book` selects the book primitive rules for
natural-number, integrality, and normalization proofs. Conditional
proofs use the selected rules on both branches. The formula solver
builds its proofs from signed tests and the Steps in Evidence.

The auxiliary dependency scan consumes characters in order, matching
quoted names and qualified symbols. Each matched chunk records its
characters and the unconsumed tail so callers can collect or substitute
tokens with the same boundaries.
