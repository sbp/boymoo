# Input state invariants

`lib` is a Library as specified in `prover/sig/library.md`, and a Step has the form in `prover/sig/proof.md`. Every function that constructs a proof can return a failure instead of its listed result. Functions that add lemmas return the extended Library.

`*t2-input-state-state*`, `*t2-input-state-true-list*`, `*t2-input-state-global-table*`, `*t2-input-state-ordered*`, `*t2-input-state-open-channels*`, `*t2-input-state-all-bound*` and `*t2-input-state-nfix*` are symbol terms for `STATE-P1`, `TRUE-LISTP`, `GLOBAL-TABLE`, `ORDERED-SYMBOL-ALISTP`, `OPEN-CHANNELS-P`, `ALL-BOUNDP` and `NFIX`. `*t2-input-state-length*`, `*t2-input-state-stringp*`, `*t2-input-state-symbolp*`, `*t2-input-state-max*`, `*t2-input-state-eq*` and `*t2-input-state-eql*` are the corresponding symbols in `COMMON-LISP`.

| ACL2 call | Arguments and result |
|---|---|
| `(t2-input-state-instantiate lib name formals actuals)` | `name` is an ACL2 fact name string, `formals` is a whitespace-separated string of formal names, and `actuals` is a list of terms in argument order. Returns the instantiated Step. |
| `(t2-input-state-tests lib proposition)` | `proposition` is a Step for a right-associated conditional conjunction. Returns the proved conjunct Steps in order, including the final proposition. |
| `(t2-input-state-closed-boolean lib term definitions)` | `term` is a closed term and `definitions` is a list of symbols to unfold, or `nil` to supply no definitions. Returns a Step for the term or its negation. |
| `(t2-input-state-list-length lib)` | Library with `SELF-LENGTH-TRUE-LIST`. |
| `(t2-input-state-length-after-write lib slot value state is-list original)` | `slot`, `value` and `state` are terms. `is-list` and `original` prove the old list condition and length. Returns the two Steps for the updated list condition and length in that order. |
| `(t2-input-state-rewrite-terms lib term direct)` | `direct` describes a term transformation. Returns an equality Step for the rewritten term, or `nil` when there is no rewriting. |
| `(t2-input-state-update-projections lib state updated)` | `state` and `updated` are terms for the old state and its `UPDATE-NTH` call. Returns the transformation `(:projections state updated)` or a failure for malformed update data. |
| `(t2-input-state-update-projections-direct term lib state updated)` | Returns the projection equality Step for `term` under that update, or `nil` when no projection applies. |
| `(t2-input-state-updated-state lib index value proof-for-changed-field)` | `index` is an unquoted slot, `value` is a term and `proof-for-changed-field` describes a transformation of a field term and its old Step. Returns a Step proving the state invariant after the update. |
| `(t2-input-state-ordered-write lib table key value ordered key-symbol)` | `table`, `key` and `value` are terms, and `ordered` and `key-symbol` are evidence Steps. Returns a Step for the order of the table after the write. |
| `(t2-input-state-state-writes lib)` | Library with `SELF-LENGTH-TRUE-LIST`, `SELF-STATE-P1-INPUT-TABLE-WRITE` and `SELF-STATE-P1-GLOBAL-WRITE` in that order. |
| `(t2-input-state-state-writes-new-channel-table test previous can-open)` | Returns `can-open` if its first literal is `test`, or a failure. `previous` is the old field Step. |
| `(t2-input-state-state-writes-unaffected-lookup term lib globals-after globals-before)` | Returns a Step rewriting a recognized lookup in the new global table, or `nil`. The two table terms have the same roles as in `state-writes`. |
| `(t2-input-state-state-writes-global-change test previous lib globals-before globals-after symbolic-key)` | Returns the Step for the new field `test` using the old field Step `previous`, the two table terms and the key's symbol evidence Step. |
| `(t2-input-state-keep-print-state-on-path value tests lib initial assumed)` | Returns a Step for the invariant on state term `value` along an oracle and global-write path. `tests` is the list of signed tests, `initial` is the oracle result Step and `assumed` is the starting invariant Step. |
| `(t2-input-state-keep-print-state lib)` | Library with `SELF-STATE-P1-PRINT-ORACLE`. |
| `(t2-input-state-build lib)` | Library with the state and length lemmas above in the order of the build. |

`rewrite-terms` accepts a projection transformation, `(:unaffected-lookup globals-after globals-before)`, or a list of `(term . result)` replies. `updated-state` accepts `(:new-channel-table can-open)`, `(:global-change globals-before globals-after symbolic-key)`, or a list of `((term previous) . result)` replies. A reply `result` is a Step, `nil`, or a failure. Lists of replies retain insertion order.

`update-projections` returns `(:projections state updated lib)`, capturing the
Library passed when the transformation is created. The projection, lookup
and global-change transformations each accept this last Library field.
The short forms use the Library of the caller.

`(t2-input-state-tests-first lib proposition term)` returns the first yielded
Step whose first literal equals `term`. The traversal ends at that Step. It
returns a failure if no Step matches or proof construction fails.
