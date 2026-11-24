# Strict symbol sort order

`lib` is a Library as specified in `prover/sig/library.md`. A term, a symbol, and a Step have the forms in `prover/sig/proof.md`. In the results below, `(cons value lib)` carries the returned value and the Library with the definitions, facts, and entries added by the call. Entries are in append order, and fact and definition maps are in insertion order. A failure is the entire result.

| ACL2 call | Result | Failure |
|---|---|---|
| `(b2-sort-order-sort-order lib formula)` | Pair of the Step for the strict merge-sort order formula and the resulting Library. | Failure from reading the formula or constructing the proof. |
| `(b2-sort-order-lower element lst)` | Term for the head bound on `lst` by `element`. Both arguments are terms. | — |
| `(b2-sort-order-follows prefix suffix)` | Term for the head of `prefix` bounding `suffix`. Both arguments are terms. | — |
| `(b2-sort-order-nil-from-symbol-list lib lst atom typed)` | A Step showing an atomic symbol list is NIL. `lst` is a term and `atom` and `typed` are Steps for its atomicity and symbol-list type. | Failure from proof construction. |
| `(b2-sort-order-typed-parts lib lst cons typed)` | List of the Steps for the head type and tail type, in that order. `lst` is a term and `cons` and `typed` are Steps for nonemptiness and symbol-list type. | Failure from proof construction. |
| `(b2-sort-order-ordered-parts lib lst cons sorted-proof)` | List of the Steps for the head bound and tail order, in that order. `lst` is a term and `cons` and `sorted-proof` are Steps for nonemptiness and strict order. | Failure from proof construction. |
| `(b2-sort-order-prepend-ordered lib pair tail-type tail-order bound)` | Step for strict order of the cons term `pair` from the tail type, tail order, and head bound Steps. | Failure from reading the pair or constructing the proof. |
| `(b2-sort-order-prepend-descending lib pair old-descending order)` | Step for descending order of the cons term `pair` from the tail order and head bound Steps. | Failure from reading the pair or constructing the proof. |
| `(b2-sort-order-reverse-order lib)` | Pair of the name of the reverse-append order lemma and the resulting Library. | Failure from constructing the definition, measure, or proof. |
| `(b2-sort-order-merge-order lib)` | Pair of the name of the merge order lemma and the resulting Library. | Failure from proof construction. |
| `(b2-sort-order-partition-type lib)` | Pair of the name of the even- and odd-position symbol-list lemma and the resulting Library. | Failure from proof construction. |

The symbol constants are `*b2-sort-order-symbol-list*`, `*b2-sort-order-symbol-less*`, `*b2-sort-order-sorted*`, and `*b2-sort-order-descending*`.
