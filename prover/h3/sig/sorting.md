# Symbol sorting

A Library, Step and term have the forms in `prover/sig/`. Rule names are
listed in citation order. A result `(cons value lib)` carries the Library
with any entries registered by the call. A failure is the entire result.

| ACL2 call | Arguments and result | Failure |
|---|---|---|
| `(h3-sorting-register lib label claim step guards)` | Library, unprefixed label string, claim term, proof Step and guard term list. Returns `(cons name lib)` with the registered lemma name. | A failure from constructing the entry. |
| `(h3-sorting-symbol-list-rules lib)` | Library. Returns `(cons names lib)` with selector, tail, constructor, head and empty-list rules. | A failure from constructing the entries. |
| `(h3-sorting-symbol-list-reverse lib names)` | Library and rule names. Returns `(cons name lib)` with the reverse rule. | A failure from constructing the proof. |
| `(h3-sorting-skips-one lib variable)` | Library and formal variable. Returns the Step for the two CDRs decreasing the count. | A failure from constructing the proof. |
| `(h3-sorting-evens-types lib names)` | Library and rule names. Returns `(cons name lib)` with the even-position type rule. | A failure from constructing the proof. |
| `(h3-sorting-evens-bound lib)` | Library. Returns `(cons (list weak-name strict-step) lib)` with the weak length rule and its strictly decreasing use. | A failure from constructing the proof. |
| `(h3-sorting-symbol-sort lib formula)` | Library and symbol-sort type formula. Returns `(cons step lib)`. | A failure from inspecting the formula or constructing the proof. |

The constants `*h3-sorting-evens*`, `*h3-sorting-odds*`,
`*h3-sorting-merge*`, `*h3-sorting-revappend*` and `*h3-sorting-symbolp*`
are prover symbols.
