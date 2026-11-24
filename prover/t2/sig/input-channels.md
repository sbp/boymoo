# Input channel tables

Terms, Steps and the Library use the forms in `prover/sig/proof.md` and
`prover/sig/library.md`. The prover symbols for the table predicates and state
update are `*t2-input-channels-symbol-alist*`,
`*t2-input-channels-open-list*`, `*t2-input-channels-open-entry*` and
`*t2-input-channels-update-input*`.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t2-input-channels-car term)` | The Common Lisp `CAR` call on the term. | None. |
| `(t2-input-channels-cdr term)` | The Common Lisp `CDR` call on the term. | None. |
| `(t2-input-channels-after-atom-test lib equation shape)` | Select the branch of the equation Step using the signed `CONSP` Step `shape`. | A failure from proof construction. |
| `(t2-input-channels-list-tests lib evidence shape)` | The proved components in conjunction order from the list predicate Step `evidence` and its signed `CONSP` Step `shape`. | A failure from proof construction. |
| `(t2-input-channels-cons-proof lib pair)` | A `CONSP` Step for the `CONS` term `pair`. | A failure from proof construction. |
| `(t2-input-channels-typed-lookup lib)` | Library with the typed channel lookup lemma. | A failure from proof construction. |
| `(t2-input-channels-prefix-table lib entry head tail)` | An open-channel-list Step for the `CONS` of the entry term and the table proved by `tail`. `head` proves the entry's type. | A failure from proof construction. |
| `(t2-input-channels-typed-write lib)` | Library with the typed channel write lemma. | A failure from proof construction. |
| `(t2-input-channels-typed-pop lib)` | Library with the typed channel object removal lemma. | A failure from proof construction. |
| `(t2-input-channels-read-channel-table lib)` | Library with the channel table preservation lemma. | A failure from proof construction. |
| `(t2-input-channels-preserve-read-state lib)` | Library with the state preservation lemma. | A failure when the state proof lacks a matching channel conjunct or proof construction fails. |
| `(t2-input-channels-build lib)` | Library with the input channel lemmas in recipe order. | A failure from proof construction. |
