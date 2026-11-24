# Ordinal expansion

The constants `*h4-book-expansion-e0-ordinal*`, `*h4-book-expansion-e0-less*`, `*h4-book-expansion-copy*`, `*h4-book-expansion-ctoa*`, and `*h4-book-expansion-expansion-order*` are the symbols `E0-ORDINALP`, `E0-ORD-<`, `COPYN`, `CTOA`, and `H4-EXPANDED-ORDINAL-ORDER` in the ACL2 package of the prover terms. The constants for the run comparison variables are `*h4-book-expansion-element*`, `*h4-book-expansion-first-count*`, and `*h4-book-expansion-second-count*`.

`p` is a Library with H4 proof methods. Steps and terms use the forms in `prover/sig/proof.md`. The following functions leave `p` unchanged.

| ACL2 call | Result | Failure |
|---|---|---|
| `(h4-book-expansion-active-count p positive)` | Step proving that the countdown on the argument of the `POSP` Step `positive` is active. | A failure from proof construction. |
| `(h4-book-expansion-copied-prefix p element count tail test)` | Equality Step that opens the outer constructor of `APPEND(COPYN(element, count), tail)`, using the countdown test Step `test`. | A proof failure. |
| `(h4-book-expansion-compare-expansions p theorem first second)` | Two equality Steps in forward and backward order, using the comparison theorem Step and the two ordinal type Steps. | A proof failure. |
| `(h4-book-expansion-expansion-shape formula)` | A one-element subject list for a type theorem, two subjects in left-to-right order for an order theorem, or `nil` for no match. | A failure from reading a malformed term. |

An OrdinalExpansion has the form `(:h4-ordinal-expansion ordinal subject shape is-pair converted power count rest element suffix opened pieces spine)`. Use the constructor and accessors below. Its `pieces` field is an alist keyed by literal, with Steps as values, in conjunct order. A later occurrence of a key replaces the value in place. The field is empty in the atom case.

| ACL2 call | Result | Failure |
|---|---|---|
| `(h4-book-expansion-ordinal-expansion-init p ordinal shape)` | OrdinalExpansion of an ordinal type Step and a Step specifying the shape of its subject. | A proof failure. |
| `(h4-book-expansion-ordinal-expansion-ordinal view)` | The ordinal type Step. | None. |
| `(h4-book-expansion-ordinal-expansion-subject view)` | The ordinal term. | None. |
| `(h4-book-expansion-ordinal-expansion-shape view)` | The shape Step. | None. |
| `(h4-book-expansion-ordinal-expansion-is-pair view)` | `t` for the cons case, `nil` for the atom case. | None. |
| `(h4-book-expansion-ordinal-expansion-converted view)` | The expansion call on the subject. | None. |
| `(h4-book-expansion-ordinal-expansion-power view)` | The leading exponent call on the subject. | None. |
| `(h4-book-expansion-ordinal-expansion-count view)` | The leading coefficient call on the subject. | None. |
| `(h4-book-expansion-ordinal-expansion-rest view)` | The remaining ordinal call on the subject. | None. |
| `(h4-book-expansion-ordinal-expansion-element view)` | The expansion call on the leading exponent. | None. |
| `(h4-book-expansion-ordinal-expansion-suffix view)` | The expansion call on the remaining ordinal. | None. |
| `(h4-book-expansion-ordinal-expansion-opened view)` | The equality Step opening the expansion. | None. |
| `(h4-book-expansion-ordinal-expansion-pieces view)` | The alist of component Steps. | None. |
| `(h4-book-expansion-ordinal-expansion-spine view)` | The equality Step opening the outer constructor of the expansion. | None. |
| `(h4-book-expansion-ordinal-expansion-power-type view)` | The ordinal type Step for the leading exponent. | A failure for a missing component. |
| `(h4-book-expansion-ordinal-expansion-rest-type view)` | The ordinal type Step for the remaining ordinal. | A failure for a missing component. |
| `(h4-book-expansion-ordinal-expansion-rational-if-finite view p)` | The rationality Step for the finite subject. | A proof failure. |
| `(h4-book-expansion-ordinal-expansion-natural-count view p)` | The natural-number Step for the leading coefficient. | A failure from proof construction or a missing component. |

An ExpansionProofs has the form `(:h4-expansion-proofs reflexive order)` with `nil` for each unprepared Step. Use its constructor and accessors. The first preparation adds the expansion order lemma to both the fact map and the entry list. A prepared object adds its stored clause to the fact map.

| ACL2 call | Result | Failure |
|---|---|---|
| `(h4-book-expansion-expansion-proofs-init)` | An unprepared ExpansionProofs object. | None. |
| `(h4-book-expansion-expansion-proofs-reflexive expansions)` | The stored irreflexivity Step or `nil`. | None. |
| `(h4-book-expansion-expansion-proofs-order expansions)` | The stored comparison Step or `nil`. | None. |
| `(h4-book-expansion-expansion-proofs-prepare expansions p)` | `(list expansions p)` with the resulting ExpansionProofs and Library. | A failure from proof construction. |
| `(h4-book-expansion-expansion-proofs-prove expansions p formula support)` | `(list step expansions p)` with a Step or `nil` and the resulting ExpansionProofs and Library. `support` is a fact alist in insertion order, with `(name . clause)` entries. The result carries the original facts and any added entry. | A failure from proof construction. |

A failure is the entire result in place of either result list.
