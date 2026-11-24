# Structural list proofs

`lib` is the library used by the T2 tactics, and terms and Steps use the
shared proof representation. A pair `(cons result lib)` carries the result
and the library after adding any auxiliary lemmas. A failure
is the entire result.

The symbol constants are `*t2-structural-lists-append*`,
`*t2-structural-lists-symbol-alistp*`, `*t2-structural-lists-true-listp*`,
`*t2-structural-lists-revappend*`, `*t2-structural-lists-merge*`,
`*t2-structural-lists-sort*`, `*t2-structural-lists-symbol-less*` and
`*t2-structural-lists-acc*`. The alist `*t2-structural-lists-fields*`
maps `SYMBOL-ALISTP` to 3 and `TRUE-LISTP` to 1, in that order.

| Call | Result | Failure |
|---|---|---|
| `(t2-structural-lists-constructed term)` | Boolean indicating that `term` is quoted NIL or a `CONS` call. | None. |
| `(t2-structural-lists-append-associativity lib)` | Pair of the lemma name string and library. Adds the associativity lemma if absent. | A proof failure. |
| `(t2-structural-lists-append-to-empty lib)` | Pair of the lemma name string and library. Adds the right identity lemma for a true list if absent. | A proof failure. |
| `(t2-structural-lists-preserve-list-predicate lib operation predicate)` | Pair of the lemma name string and library. `operation` is the append or reverse append symbol and `predicate` is a symbol in `fields`. | A proof failure. |
| `(t2-structural-lists-predicate-tail lib predicate)` | Pair of the lemma name string and library for a `predicate` in `fields`. | A proof failure. |
| `(t2-structural-lists-evens-preserves lib formula)` | Pair of a Step for the `EVENS` preservation formula and library. | A proof failure. |
| `(t2-structural-lists-merge-preserves lib formula)` | Pair of a Step for the merge preservation formula and library. | A proof failure. |
| `(t2-structural-lists-sort-preserves lib formula)` | Pair of a Step for the sort preservation formula and library. | A proof failure. |
| `(t2-structural-lists-prove lib formula)` | Pair of a Step or `nil` and library. Selects the proof by the operation in the `SYMBOL-ALISTP` conclusion of `formula`, or returns `(cons nil lib)` if no recipe applies. | A proof failure. |

## Lifted expansion predicates

Each predicate takes a call term and its listed bindings and returns a
Boolean. Term indexing can fail on malformed calls.

| Call | Accepted terms |
|---|---|
| `(t2-structural-lists-append-associativity-expand call)` | An append whose first argument is `X` or constructed. |
| `(t2-structural-lists-preserve-list-predicate-expand call operation predicate)` | An application of `operation` to `X` first, or of `predicate` to a constructed term. |
| `(t2-structural-lists-evens-preserves-expand call term)` | The term itself, or a `SYMBOL-ALISTP` call on a constructed term. |
| `(t2-structural-lists-merge-preserves-expand call term predicate)` | The term itself, or a `predicate` call on a constructed term. |
| `(t2-structural-lists-sort-preserves-expand call term predicate)` | The term itself, or a `predicate` call on quoted NIL. |
