# Hanoi proofs

`p` is the Library used by H4 Tactics. Terms and Steps have the forms in
`prover/sig/proof.md`. An evidence map is an association list from the first
literal of a Step to that Step. The map stays in insertion order when a
value is replaced.

| Function | Arguments and result | Failure |
|---|---|---|
| `(h4-book-hanoi-hanoi-proof p formula uses)` | Prove a Hanoi transfer invariant or corollary. `uses` is the list of hint uses for `formula`, as in `book-hints.md`. The result is a Step or `nil`. | Propagates a failure from the transfer proof, or from corollary preparation. |
| `(h4-book-hanoi-hanoi-corollary p formula uses)` | Prove the equality `formula` by instantiating the first implication among the hint facts. The result is a Step or `nil`. | Propagates a failure from preparation. The case-proof fallback kinds in `prover/h4/notes/failures.md` yield `nil`. |
| `(h4-book-hanoi-stack-transfer p formula)` | Prove the stack-transfer implication by induction. Returns a Step. | May return a failure. |
| `(h4-book-hanoi-hanoi name)` | Return the symbol with string name `name` in package `HANOI`. | None. |
| `(h4-book-hanoi-cons-list items)` | Return the term that constructs the list of terms in `items`, in argument order. | None. |
| `(h4-book-hanoi-index-membership p index evidence)` | Return a Step proving the `MEM` call for the index term `index` in the three slots, using the evidence map. | May return a failure. |
| `(h4-book-hanoi-top-bound size stack)` | Return the bound term for disk size term `size` and stack term `stack`. | None. |
| `(h4-book-hanoi-bound-under-step p bound decrease transitive)` | Use the Steps `bound`, `decrease` and `transitive` to prove the stack bound for the smaller size. | May return a failure. |
| `(h4-book-hanoi-added-tower p state index tower countdown)` | Prove the update that exposes the largest disk. `state` is a TransferState, `index` and `tower` are terms, and `countdown` is an equality Step. | May return a failure. |

A TransferState has the form
`(:h4-transfer-state p natural true-list length permutation slots size base top-bounds evidence indexed constructors)`.
`natural`, `true-list`, `length` and `permutation` are Steps. `slots` is the
list of index terms in premise order. `size` and `base` are terms.
`top-bounds` is the ordered map from slot terms to their bound Steps.
`evidence` is the ordered evidence map, `indexed` is an IndexedState, and
`constructors` is the constructor reduction provider.

| Function | Arguments and result | Failure |
|---|---|---|
| `(h4-book-hanoi-transfer-state-init p premise)` | Construct a TransferState from Library `p` and the transfer premise term. | May return a failure. |
| `(h4-book-hanoi-transfer-state-reduce self term)` | Return a reduction Step for `term`, or `nil`. Try constructor, indexed state and append reductions in that order. | May return a failure. |
| `(h4-book-hanoi-transfer-state-stack self index)` | Return the stack lookup term for the index term `index`. | None. |
| `(h4-book-hanoi-transfer-state-permutation-given self order)` | Prove the slot permutation in term list `order`. | May return a failure. |
| `(h4-book-hanoi-transfer-state-amended self slot)` | Return the state update term for adding the disk to slot term `slot`. | None. |
| `(h4-book-hanoi-transfer-state-smaller-tops self decrease)` | Return a map from each slot to the smaller bound Step, in premise slot order. `decrease` is a strict-comparison Step. | May return a failure. |
| `(h4-book-hanoi-transfer-state-amended-guards self order state smaller-nat decrease smaller-tops)` | Prove the guards for permutation term list `order` and amended state term `state`, using the natural and decrease Steps and the smaller-bound map. | May return a failure. |
| `(h4-book-hanoi-transfer-state-move-fields self move source destination)` | Return the two Steps equating the move fields to terms `source` and `destination` in that order. `move` is a term. | May return a failure. |
| `(h4-book-hanoi-transfer-state-legal-move self move state source destination access)` | Prove the legality of the terms `move` and `state` using the source and destination terms and their ordered list of `access` Steps. | May return a failure. |

The two Hanoi tactic calls above use an empty constrained and chosen function
set. For a caller that has this set, use
`(h4-book-hanoi-hanoi-proof-with-book-functions p formula uses book-functions)`
or `(h4-book-hanoi-hanoi-corollary-with-book-functions p formula uses book-functions)`.
The additional argument is the function-name set from `book-hints.md`. The
result and failures follow the corresponding three-argument call. The
TransferState constructor provider stores the equality Step for CONSP of a
CONS expression, with the Library already present in the state.
