# Bounds for a split list

`lib` is a Library and Steps and terms have the forms in `prover/sig/library.md`
and `prover/sig/proof.md`. `*t3-book-halves-aux*` and `*t3-book-halves-halve*`
are the symbols for the auxiliary and public split functions in package `SET`.
`*t3-book-halves-mv-nth*` and `*t3-book-halves-zp*` are ACL2 symbols.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t3-book-halves-length-cons lib value cons)` | A Step for opening `LEN` on term `value`. Pass a branch Step as `cons`, or `nil` to normalize without one. | A failure from constructing the Step. |
| `(t3-book-halves-length-weak lib)` | The Library with the weak length bound for `CDR`. | A failure from constructing or adding the lemma. |
| `(t3-book-halves-split-bound lib index)` | The Library with the length bound for result `index` of the split auxiliary. | A failure from constructing or adding the lemma. |
| `(t3-book-halves-split-bound-leaf value tests lib index fixed-index measure next-fast added formula pairs)` | The Step for a leaf term `value` under the signed `tests` of the split auxiliary. `fixed-index` is the quoted index, `measure` is the count term, `next-fast` and `added` are the updated fast cursor and accumulator, `formula` is the induction formula, and `pairs` is the ordered list of induction bindings. | A failure from constructing the leaf proof. |
| `(t3-book-halves-halves lib)` | The Library with the auxiliary and public split bounds in proof order. | A failure from constructing or adding a lemma. |
