# Character-list proofs

Terms and Steps have the forms in `prover/sig/proof.md`. The `proof` argument is the H2 proof object used for search and auxiliary lemmas. A result written `(cons value proof)` carries the resulting proof object, with any updates to the search or auxiliary lemmas. A failure can appear in the value position. `rules` contains the cons and append fact name strings in that order. `leaves` contains applicable fact name strings in order. `evidence` is a list of Steps in the order given.

| Call | Result |
|---|---|
| `(h2-characters-character-constructors proof)` | `(cons rules proof)` with the ordered pair of fact name strings and the proof object with the constructor lemmas. |
| `(h2-characters-character-digits proof rules)` | `(cons name proof)` with the integer printing invariant's fact name string and the proof object with its supporting lemmas. |
| `(h2-characters-character-value proof value rules leaves evidence)` | `(cons step proof)` proving that the result term `value` is a character list. |
| `(h2-characters-character-result proof opening rules leaves evidence)` | `(cons step proof)` proving the character-list invariant of the left side of the equation Step `opening`. |
| `(h2-characters-character-atom proof rules)` | `(cons name proof)` with the atom printing invariant's fact name string and the proof object with its supporting lemmas. |
| `(h2-characters-pack-characters proof function variable)` | `(cons step proof)` proving `CHARACTER-LISTP` for the given packing function symbol applied to `variable`. |

The symbol constants are `*h2-characters-char*`, `*h2-characters-rational*`, `*h2-characters-numerator*`, `*h2-characters-real*`, `*h2-characters-imag*`, `*h2-characters-char-list*`, `*h2-characters-proper*`, `*h2-characters-append*`, `*h2-characters-digit*`, `*h2-characters-atom-text*`, `*h2-characters-pack-list*` and `*h2-characters-pack-tree*`.

The proof argument is the Search in `prover/h2/sig/search.md`. The value of a result pair can be a Search hook request. In addition to proof search hooks, a BookProof caller can enable the following hooks for the state of the enclosing proof object.

| Method | Request arguments | Reply value and effect |
|---|---|---|
| `:set-fuel` | The new rewriting budget | `nil`, with the BookProof using that budget. |
| `:keep-folded` | List of terms | The original fixed-call set, with the BookProof using its union with the terms. |
| `:restore-fixed-calls` | The original fixed-call set | `nil`, with the original set restored. |

Supply each reply as `(:return value)`. If the BookProof supplies the `:keep-folded` hook, it also supplies `:restore-fixed-calls`.

| Lifted call | Result |
|---|---|
| `(h2-characters-character-digits-character-at value tests proof)` | Step establishing the character type of the quoted digit `value`, or a failure. |
| `(h2-characters-character-digits-recognize claim evidence proof rules)` | `(cons step proof)` with the proof of `claim` from the accumulator invariant Step `evidence`. |
| `(h2-characters-character-result-at-leaf value tests proof rules leaves evidence)` | `(cons step proof)` for the result term `value` under the additional signed tests, in their path order. |
| `(h2-characters-pack-characters-shape holds evidence proof test formula rules atom)` | `(cons step proof)` proving the joint packing formula under the sign `holds` of `test`. `atom` is the name string for the atom printing invariant. |
