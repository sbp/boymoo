# List truncation

`*b2-butlast-butlast*`, `*b2-butlast-take*`, `*b2-butlast-nfix*` and
`*b2-butlast-zp*` are prover symbols. The library has the form in
`prover/sig/library.md`. Formulas, terms, and Steps have the forms in
`prover/sig/proof.md`.

A Truncation object has the form
`(:b2-butlast-truncation lib index fixed natural integer nonnegative)`.
`fixed` is the NFIX call on `index`, and the three following fields are Steps
about that call. The functions use the library stored in the object.
`b2-butlast-truncation-lib`, `b2-butlast-truncation-index`,
`b2-butlast-truncation-fixed`, `b2-butlast-truncation-natural`,
`b2-butlast-truncation-integer`, and `b2-butlast-truncation-nonnegative`
take the object and return the corresponding field.

| Function | Arguments and result | Failure |
|---|---|---|
| `(b2-butlast-normalized-index lib term)` | Library and index term. Returns `(cons step lib)`, where the Step proves naturalness of `(NFIX term)` and the resulting library includes any new lemma. | Proof construction. |
| `(b2-butlast-integer-after-successor lib ordered types)` | Library, Step for `a < b`, and integer evidence Steps. Returns the Step for `1 + a <= b`. | Proof construction. |
| `(b2-butlast-truncation-init lib index)` | Library and index term. Returns a Truncation object containing the library after any lemma addition. | Proof construction. |
| `(b2-butlast-truncation-take truncation lst)` | Truncation and list term. Returns the TAKE term corresponding to BUTLAST. | — |
| `(b2-butlast-truncation-count-test truncation length comparison want-positive)` | Truncation, length term, comparison Step, and Boolean telling whether the count is positive. Returns the signed ZP Step. | Proof construction. |
| `(b2-butlast-truncation-empty truncation lst atom)` | Truncation, list term, and Step stating the list is an atom. Returns the equality of BUTLAST to NIL. | Proof construction. |
| `(b2-butlast-truncation-take-equals-butlast truncation lst)` | Truncation and list term. Returns the Step equating BUTLAST to TAKE. | Proof construction. |
| `(b2-butlast-truncation-selector truncation formula)` | Truncation and selector formula. Returns its Step. | Proof construction. |
| `(b2-butlast-truncation-cons truncation formula)` | Truncation and BUTLAST-OF-CONS formula. Returns its Step. | Proof construction. |
| `(b2-butlast-truncation-cdr truncation formula)` | Truncation and CDR-OF-BUTLAST formula. Returns its Step. | Proof construction. |
| `(b2-butlast-prove-butlast lib name formula)` | Library, theorem symbol, and formula. Returns `(cons step lib)` including any lemma added to the library. | Proof construction. |
