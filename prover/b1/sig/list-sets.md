# Append membership and intersection

`lib` is a Library as specified in `prover/sig/library.md`. Terms and Steps
have the forms in `prover/sig/proof.md`. A successful pair has the Step as
its `car` and the Library with any auxiliary lemmas as its `cdr`.
Each function can return a failure value `(:failure kind message)` in
place of the entire result.

| ACL2 call | Arguments and result |
|---|---|
| `(b1-list-sets-append-membership-cases lib formula driver first second intersection)` | Given a claim term, its list induction term `driver`, and the two lists `first` and `second` tested for membership, return `(cons step lib)`. Pass `:none` for an omitted `intersection`, or the term for the list intersected with the tail of `driver`. |
| `(b1-list-sets-no-duplicate-append lib formula)` | Return `(cons step lib)` for the duplicate-free append claim. |
| `(b1-list-sets-intersect-append lib formula)` | Return `(cons step lib)` for the intersection claim with an append in its second argument. |
| `(b1-list-sets-appended-first-intersection lib formula)` | Return the Step for the intersection claim with an append in its first argument. |
| `(b1-list-sets-intersection-with-extended-second lib formula)` | Return the Step for the intersection claim with a new head in its second argument. |

`*b1-list-sets-member*`, `*b1-list-sets-intersect*`, `*b1-list-sets-a*`
and `*b1-list-sets-b*` are the ACL2 symbol terms `MEMBER-EQUAL`,
`INTERSECTP-EQUAL`, `A` and `B`, respectively.
