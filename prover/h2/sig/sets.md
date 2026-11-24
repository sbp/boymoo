# List-based set relations

`proof` is the proof-search object described in `prover/h2/sig/search.md`.
Terms and Steps have the forms in `prover/sig/proof.md`. A pair in the
result column is constructed with `cons`. Each call can return a failure
as its entire result.

| Call | Result |
|---|---|
| `(h2-sets-subset-laws proof)` | Pair of the three fact name strings for reflexivity, transitivity and Boolean type, in that order, and the resulting proof. |
| `(h2-sets-subset-fix proof)` | Pair of the two fact name strings for fixing the left and right inputs of `SUBSETP-EQUAL`, in that order, and the resulting proof. |
| `(h2-sets-set-equivalence proof formula laws)` | Pair of the Step for the set equivalence law `formula` and the resulting proof. `laws` is the name list from `h2-sets-subset-laws`. |
| `(h2-sets-list-to-set proof formula reflexive)` | Pair of the Step for the refinement `formula` and the resulting proof. `reflexive` names the reflexive subset fact. |
| `(h2-sets-set-theorem proof label formula)` | Pair of the Step or `nil` and the resulting proof. `label` is the theorem's unqualified name string. The recognized labels are `SET-EQUIV-IS-AN-EQUIVALENCE`, `LIST-EQUIV-REFINES-SET-EQUIV`, `SUBSETP-REFL`, and `SUBSETP-TRANS`. |
| `(h2-sets-set-equivalence-type-at-leaf value tests nil-boolean proof laws)` | A Boolean type Step for leaf term `value`. `tests` is the list of signed tests in scope, `nil-boolean` is a Boolean type Step for quoted `NIL`, and `laws` is the name list above. |

Fact names, Steps, and terms retain their argument or traversal order.

A Search with inherited method hooks may yield a Search request as the
entire result. Replay with the ordered replies as described in
`prover/h2/sig/search.md`. A successful pair preserves the unused replies
in its Search.
