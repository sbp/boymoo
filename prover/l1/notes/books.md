# Obligation dependencies

The formula tactic first uses simplification according to the Proof kind. If simplification has no proof, the tactic looks for a matching fact, handles an implication, or tries rewriting when enabled.

`l1-books-fact-names` reads `fact` lines in the certificate. It recognizes LF, CR, and CRLF line breaks and orders the names by the ACL2 text of their data. Arithmetic helpers are emitted in library order. The helper calculation includes dependencies cited by those helpers.
