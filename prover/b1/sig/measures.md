# Measures for recursive calls

`lib` is a B1 Library. Terms and Steps follow `prover/sig/proof.md`.
Definitions and Calls follow `prover/sig/termination.md`. Both `aids`
and `measures` are insertion-ordered association lists of
`(name . measure)` pairs. A plan is a measure alist.

A B1 Rulers object is `(:b1-measures-rulers hypotheses)`, where
`hypotheses` has the form in `prover/sig/descent.md` and holds the
Library, signed tests, extra evidence, and evidence established by queries.
The evidence maps retain insertion order. Use the constructor and accessors
below. A signed test is a two-element list `(term holds)`.

| ACL2 call | Result | Failure |
|---|---|---|
| `(b1-measures-rulers-init lib tests extra)` | Rulers with the signed tests `tests` and list of Steps `extra`. Pass `nil` for an empty list of additional Steps. | A failure from reading a Step. |
| `(b1-measures-rulers-proof rulers)` | The Library of the Rulers. | None. |
| `(b1-measures-rulers-tests rulers)` | The signed tests of the Rulers. | None. |
| `(b1-measures-rulers-with-proof rulers lib)` | Rulers with Library `lib` and the same tests and evidence. | None. |
| `(b1-measures-rulers-find rulers term)` | `(cons step rulers)` with the Step for `term` or `nil`, and the resulting Rulers. | A failure from constructing evidence. |
| `(b1-measures-rulers-require rulers term)` | `(cons step rulers)` with the Step for `term` and the resulting Rulers. | A failure if evidence is missing or cannot be constructed. |
| `(b1-measures-constant-member lib term)` | An equality Step for a `MEMBER-EQUAL` call on quoted arguments, or `nil`. | A failure from proof construction or `Fuel`. |
| `(b1-measures-count-descent lib goal hypotheses)` | Step for the strict count comparison term `goal`, under the signed tests of the B1 Rulers `hypotheses`. | `Unproved` for a missing descent recipe, a failure from proof construction, or `Fuel`. |
| `(b1-measures-proof-for-measures lib definitions calls measures)` | `(cons (list measure-list proofs) lib)` with the resulting Library. The measure list is in definition order, and the Steps follow the order of first occurrence of the obligation clauses. | A failure from reading or proving an obligation or `Fuel`. |
| `(b1-measures-measure-plans definitions calls aids)` | List of plans in the order they are tried. The aided plan follows definition order, the selector plan follows the order of the selector alist, and the single-formal plans follow formal order. | A failure from reading definitions, Calls or aids. |
| `(b1-measures-termination lib definitions calls aids)` | The same pair as `b1-measures-proof-for-measures`, for the first successful plan. | `Unproved` when the plans fail, a failure from proof construction, or `Fuel`. |

The prover symbols are `*b1-measures-member*` and
`*b1-measures-hard-error*`.

`(b1-measures-termination-with-library lib definitions calls aids)`
takes the same arguments as `b1-measures-termination` and always
returns `(cons result lib)`. Its result is the list of measures and
proofs or a failure. The Library includes auxiliary lemmas from attempts
made before the selected proof or the final failure.
