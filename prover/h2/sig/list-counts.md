# List count proofs

Terms and Steps have the forms in `prover/sig/proof.md`. The `proof` argument is the H2 proof object used for search and auxiliary lemmas. A result written `(cons value proof)` carries the resulting proof object, including any search configuration or auxiliary lemmas. A failure occupies the value position of a pair or the whole result of a call that returns a Step directly.

| Call | Result |
|---|---|
| `(h2-list-counts-list-branch proof call shape cons-p)` | `(cons step proof)` with the selected equation for `call`. `shape` proves cons or noncons as indicated by the Boolean `cons-p`. |
| `(h2-list-counts-count-call key data)` | The term `(DUPLICITY key data)`.  |
| `(h2-list-counts-count-case proof opening evidence)` | `(cons step proof)` with the selected branch of the equation Step `opening`, given the Step `evidence` for the comparison or its negation. |
| `(h2-list-counts-cons-count proof key head tail)` | Step citing the count for `key` in a cons with the given head and tail terms. |
| `(h2-list-counts-append-count proof key first second)` | Step citing the count for `key` in an append of the two list terms. |
| `(h2-list-counts-natural-count proof key data)` | `(cons step proof)` with the natural count Step for `key` in `data`, and the natural count lemma added on first use. |
| `(h2-list-counts-count-integer proof key data)` | `(cons step proof)` with the integer count Step for `key` in `data`. |
| `(h2-list-counts-accumulator-count proof formula)` | `(cons step proof)` proving the accumulator equation. |
| `(h2-list-counts-sum-counts proof formula operation)` | `(cons step proof)` proving the count sum formula for the append or reverse-append symbol `operation`. |
| `(h2-list-counts-count-fixed-list proof formula)` | `(cons step proof)` proving the count invariant under list fixing. |
| `(h2-list-counts-member-count proof formula present)` | `(cons step proof)` proving the corresponding formula, with Boolean `present` selecting membership or its negation. |
| `(h2-list-counts-count-zero-iff proof formula)` | `(cons step proof)` proving the equivalence between zero count and absence. |
| `(h2-list-counts-high-count proof formula)` | `(cons step proof)` proving the duplicate criterion for a high count. |
| `(h2-list-counts-drop-empty-count proof equality)` | `(cons step proof)` with the equality Step after removing the empty-list contribution on its right. |
| `(h2-list-counts-rev-count proof formula)` | `(cons step proof)` proving the count invariant under `REV`. |
| `(h2-list-counts-reverse-count proof formula)` | `(cons step proof)` proving the count invariant under `REVERSE`. |
| `(h2-list-counts-flatten-count proof formula)` | `(cons step proof)` proving the count formula for the flattening of a reversal. |
| `(h2-list-counts-count-theorem proof label formula)` | `(cons step proof)` for a recognized theorem label string, or `(cons nil proof)` for an unrecognized label. |

The symbol constants are `*h2-list-counts-duplicity*`, `*h2-list-counts-append*`, `*h2-list-counts-fix*`, `*h2-list-counts-flatten*`, `*h2-list-counts-a*`, `*h2-list-counts-b*`, `*h2-list-counts-revappend*` and `*h2-list-counts-stringp*`.

The proof argument is the Search in `prover/h2/sig/search.md`. The pure fact calls also accept a Library. A pair can carry a Search hook request in its value position. Replaying the initiating call with the ordered replies retains the unused reply suffix between successive searches.

The lifted calls are `(h2-list-counts-high-count-impossible count-value proof premise goal)` and `(h2-list-counts-reverse-count-zero-for-string term evidence proof key)`. The first takes a replacement equality and comparison premise Step and returns a Step for `goal`, or a failure. The second takes a string term and its type Step and returns `(cons step proof)` showing that its `DUPLICITY` count for `key` is zero.
