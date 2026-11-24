# Records

`*b2-records-get*`, `*b2-records-set*`, `*b2-records-get-nil*`,
`*b2-records-set-same*` and `*b2-records-set-different*` are prover
symbols. `*b2-records-record-corollaries*` is the list of the corollary
symbols in symbol-name order.
The library has the form in `prover/sig/library.md`. Formulas, terms and
Steps have the forms in `prover/sig/proof.md`.

| Function | Arguments and result | Failure |
|---|---|---|
| `(b2-records-get-nil lib key)` | Library and lookup key term. Returns the Step equating the lookup on NIL to NIL. | Missing fact assertion or proof construction. |
| `(b2-records-record-corollary lib name formula)` | Library, theorem symbol, and formula. Returns the Step for the named corollary. | Proof construction. |
| `(b2-records-record-corollary-consequent premise lib goal key value)` | Antecedent Step, Library, record update term, key term, and value term. Returns the Step for the update being non-NIL. | Proof construction. |
