# Name capacity bounds

`lib` is a Library with the T3 proof rules. `string`, `symbol` and `symbols`
are terms denoting a string, a symbol and a list of symbols, respectively.
Terms and Steps have the forms in `prover/sig/proof.md`.

| Call | Result | Failure |
|---|---|---|
| `(t3-name-bounds-name-capacity string)` | Capacity term for the characters of `string`. | None. |
| `(t3-name-bounds-symbol-capacity symbol)` | Capacity term for the name of `symbol`. | None. |
| `(t3-name-bounds-name-total symbols)` | Application of the total capacity function to `symbols`. | None. |
| `(t3-name-bounds-total-natural lib symbols)` | Step proving the total capacity is natural. | A failure from citation. |
| `(t3-name-bounds-total-integer lib symbols)` | Step proving the total capacity is integer. | A failure from proof construction. |
| `(t3-name-bounds-total-branch lib symbols test)` | Step opening the total capacity function on the branch selected by the Step `test`. | A failure from proof construction. |
| `(t3-name-bounds-total-fold lib)` | Library with the capacity fold definition followed by the lemma that its result is natural. | A failure from constructing or adding an entry. |
| `(t3-name-bounds-membership-cap lib predicate)` | Library with the capacity bound lemma for membership by the predicate symbol. | A failure from constructing or adding a lemma, including a failure for an unexpected recursive branch. |
| `(t3-name-bounds-available-member-bound lib proof)` | Step bounding the member named by the membership Step `proof` by the list's total capacity. | A failure from reading a Step or constructing the proof. |
| `(t3-name-bounds-build lib)` | Library with the fold, its natural type lemma, and the bounds for membership by symbol followed by membership by name. | A failure from a recipe. |

The prover symbols are `*t3-name-bounds-name-total*`,
`*t3-name-bounds-member-equal*`, `*t3-name-bounds-member-name*`, and
`*t3-name-bounds-symbol-name*`.
