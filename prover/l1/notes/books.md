# Obligation dependencies

The formula tactic first uses simplification according to the Proof kind. If simplification has no proof, the tactic looks for a matching fact, handles an implication, or tries rewriting when enabled.

`l1-books-fact-names` reads `fact` lines in the certificate. It recognizes LF, CR, and CRLF line breaks and orders the names by the ACL2 text of their data. Arithmetic helpers are emitted in library order. The helper calculation includes dependencies cited by those helpers.

`l1-books-prepare-book-with-cache` receives certificates and their dependency tables as explicit inputs. It can reuse a certificate when every cited fact has the recorded value and its helper names are available.
