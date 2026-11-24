# Indexed count results

A Library, Step and term have the forms in `prover/sig/`. A result
`(cons value lib)` carries the Library with any entries registered by the
call. A failure is the entire result.

| ACL2 call | Arguments and result | Failure |
|---|---|---|
| `(h3-counts-nested-calls value head)` | Term and function symbol. Returns matching subterms in preorder, retaining repeats. | A failure from inspecting the term. |
| `(h3-counts-indexed-selectors lib last)` | Library and integer upper index. Returns `(cons names lib)`. The names are the MV-NTH equality, the zero rule and the rules for indices 1 through `last`, in order. | A failure from constructing the proofs or reading the index. |
| `(h3-counts-car-at-zero lib)` | Library. Returns `(cons name lib)` with the name of the CAR-to-NTH equality. | A failure from constructing the proof. |
| `(h3-counts-indexed-count lib formula)` | Library and indexed count type formula. Returns `(cons step lib)`. | A failure from inspecting the formula or constructing the proof. |
| `(h3-counts-count-tuple lib formula)` | Library and tuple count type formula. Returns `(cons step lib)`. | A failure from inspecting the formula or constructing the proof. |

The constants `*h3-counts-mv-nth*` and `*h3-counts-evg-type*` are
prover symbols.
