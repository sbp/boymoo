# Quotient algebra

A Library, Step, and term have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. In a `known` table, each key is a literal and each
value is its Step. Entries retain first-insertion order. A pair
written `(cons step library)` returns both the Step and the resulting Library,
including any auxiliary lemmas. A failure is the entire result of a call.

| ACL2 call | Arguments and result | Failure |
|---|---|---|
| `(b2-quotient-algebra-with-forced lib premise)` | Library and premise Step. Returns the ordered evidence table after expanding the premise and its forced facts. | Failure from evidence expansion. |
| `(b2-quotient-algebra-require-nonzero lib value known)` | Library, term, and evidence table. Returns a Step proving that the term is unequal to zero. | Missing evidence or unsuccessful proof construction. |
| `(b2-quotient-algebra-inverses lib value known)` | Library, term, and evidence table. Returns two Steps as a list, for the product of the term with its reciprocal and the reverse product, in that order. | Failure from evidence lookup or proof construction. |
| `(b2-quotient-algebra-exact-quotient lib quotient ratio)` | Library, floor or truncate call, and ratio term. Returns `(cons step library)` with the equivalence between the quotient equaling the ratio and the ratio being integer. | Failure from proof construction. |
| `(b2-quotient-algebra-reciprocal-of-pair lib a b c d unit-a unit-b)` | Library, four terms, and Steps proving that `a*c` and `b*d` equal one. Returns a Step proving the reciprocal of `a*b` equals `c*d`. | Failure from proof construction. |
| `(b2-quotient-algebra-cancel-to-value lib value factor known)` | Library, value and factor terms, and evidence table. Returns a Step canceling the factor with its reciprocal. | Failure from evidence lookup or proof construction. |
| `(b2-quotient-algebra-completed-product lib term evidence)` | Library, term, and ordered list of evidence Steps. Returns an equality Step reducing a product or reciprocal, or normalizing the term when it has another form. | Failure from proof construction or `Fuel` on exhaustion. |
| `(b2-quotient-algebra-quotient-identity lib name formula)` | Library, theorem name symbol, and formula term. Returns `(cons step library)` proving the formula. | Failure from evidence lookup or proof construction. |

The external symbol constants are `*b2-quotient-algebra-exact-floor*`,
`*b2-quotient-algebra-exact-truncate*`, `*b2-quotient-algebra-zero-mod*`, and
`*b2-quotient-algebra-zero-rem*`. The list
`*b2-quotient-algebra-quotient-identities*` represents the set of theorem names
for membership tests.

`b2-quotient-algebra-reciprocal-of-pair` and
`b2-quotient-algebra-completed-product` return `(cons step library)`.
Their zero-product proofs can add the `B2-ZERO-PRODUCT` lemma.

`(b2-quotient-algebra-required-evidence known literal)` reads the Step for
the literal from the evidence table and returns a failure if it is absent.
