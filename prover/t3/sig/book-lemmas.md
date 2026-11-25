# Boolean, equivalence and cons-cell lemmas

`lib` is a Library as specified in `prover/sig/library.md`. Terms and Steps
use the forms in `prover/sig/proof.md`. Every function can return a failure in
place of its result.

| Call | Result |
|---|---|
| `(t3-book-lemmas-true-equality lib proof)` | The Step equating the established equality in the Step `proof` to quoted `T`. |
| `(t3-book-lemmas-nil-value lib denial)` | The Step equating the term denied by the Step `denial` to quoted `NIL`. |
| `(t3-book-lemmas-implication lib term consequent)` | The Step proving the implication term `term` using the Step `consequent` under its antecedent. |
| `(t3-book-lemmas-boolean-value lib)` | The Library with `T3-BOOLEAN-TRUE` added. |
| `(t3-book-lemmas-iff-elimination lib)` | The Library with `T3-IFF-LEFT` and `T3-IFF-RIGHT` added in that order. |
| `(t3-book-lemmas-cons-equality lib)` | The Library with `T3-EQUAL-CONS` added. |
| `(t3-book-lemmas-natural-fix lib)` | The Library with `T3-EXPORTED-NFIX` added. |
| `(t3-book-lemmas-set-tail lib)` | The Library with `T3-SET-TAIL-COUNT` added. |
| `(t3-book-lemmas-implies-proper-list lib term wrappers)` | A Step proving `term` if it is a recognized proper-list implication, or `nil`. `wrappers` is the list of recognizer heads visited on the current path. Pass `nil` to start. |

The symbol constants are `*t3-book-lemmas-booleanp*`, `*t3-book-lemmas-iff*`,
`*t3-book-lemmas-true-listp*`, `*t3-book-lemmas-exported-nfix*`,
`*t3-book-lemmas-setp*`, `*t3-book-lemmas-empty*`, `*t3-book-lemmas-sfix*`
and `*t3-book-lemmas-set-tail*`.

The following calls expose individual steps of these recipes. They can
return a failure.

| Call | Result |
|---|---|
| `(t3-book-lemmas-iff-direction lib equivalent opened target premise name)` | The Library with one direction added. `equivalent` is the IFF term, `opened` is the Step unfolding it, `target` and `premise` are the two terms, and `name` is the unprefixed lemma name. |
| `(t3-book-lemmas-cons-equality-different project part rhs-nil lib left whole)` | The equality Step for the unequal `part` of the two cons terms. `project` is CAR or CDR, `rhs-nil` is the Step for the conditional's false value, `left` is the first cons term, and `whole` is the equality between the two cons terms. |
| `(t3-book-lemmas-set-tail-is-empty is-nil lib empty nil-test atom definitions)` | The Step proving `empty` in the given nil-test branch. `is-nil` is the Boolean sign of term `nil-test`, `atom` is the Step denying cons recognition, and `definitions` is the list of symbols to unfold. |
