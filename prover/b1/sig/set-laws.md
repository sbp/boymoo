# Set laws

`lib` is a Library with the B1 proof methods. Terms and Steps have the
forms in `prover/sig/proof.md`. A `formula` is the claim in translated term
form. Each call can return `(:failure kind message)` in place of the entire
result. A result described as a pair is `(cons value lib)` with the
resulting Library. Keep that Library for subsequent calls so that their
facts and entries include the auxiliary lemmas in insertion order.

| ACL2 call | Result |
|---|---|
| `(b1-set-laws-memberp-as-boolean lib)` | Pair of the B1 rewrite rule for `MEMBERP-EQUAL` and the Library containing `SELF-MEMBERP-BOOLEAN`. |
| `(b1-set-laws-subset-of-extension lib formula)` | Pair of the Step for inclusion in a cons or append extension and the Library. |
| `(b1-set-laws-subset-append-singleton lib formula)` | Step for inclusion after appending a singleton to the source and adjoining its element to the destination. |
| `(b1-set-laws-subset-reflexive lib formula)` | Step for reflexivity of inclusion. |
| `(b1-set-laws-subset-transitive lib formula)` | Pair of the Step for transitivity of inclusion and the Library. |
| `(b1-set-laws-set-equal-law lib formula)` | Step for symmetry or transitivity of set equality. |
| `(b1-set-laws-subset-filter-identity lib formula)` | Step for the equality of a set operation with its fixed argument under the inclusion hypothesis. |
| `(b1-set-laws-subset-of-set-operation lib formula)` | Pair of the Step for inclusion in a union, intersection, or difference and the Library. |
| `(b1-set-laws-difference-of-disjoint lib formula)` | Step for the identity of difference on a proper list disjoint from the second list. |
| `(b1-set-laws-difference-of-redundant-cons lib formula)` | Step for the equality of differences when an element already in the second list is prepended to it. |
| `(b1-set-laws-memberp-subset lib formula)` | Pair of the Step transferring Boolean membership across inclusion and the Library. |
| `(b1-set-laws-memberp-set-equal lib formula)` | Step transferring Boolean membership across set equality. |
| `(b1-set-laws-memberp-of-set-operation lib formula)` | Pair of the Step for Boolean membership after adjoin, intersection, difference, or union and the Library. |
| `(b1-set-laws-subset-adjoin lib formula)` | Pair of the Step for inclusion of an adjoining operation and the Library. |
| `(b1-set-laws-setp-cons lib formula)` | Pair of the Step characterizing set recognition on a cons and the Library. |
| `(b1-set-laws-setp-adjoin lib formula)` | Pair of the Step preserving set recognition under adjoin and the Library. |
| `(b1-set-laws-setp-under-operation lib formula)` | Pair of the Step preserving set recognition under intersection, difference, or union and the Library. |
| `(b1-set-laws-no-duplicates-append lib formula)` | Pair of the Step for duplicate freedom of an append and the Library. |
| `(b1-set-laws-setp-append lib formula)` | Step for set recognition of an append. |

`*b1-set-laws-subset*`, `*b1-set-laws-set-equal*`,
`*b1-set-laws-memberp*`, `*b1-set-laws-adjoin*`,
`*b1-set-laws-true-listp*`, `*b1-set-laws-union*`,
`*b1-set-laws-difference*`, `*b1-set-laws-setp*`, and
`*b1-set-laws-no-duplicates*` are the term symbols `SUBSETP-EQUAL`,
`SET-EQUAL`, `MEMBERP-EQUAL`, `ADJOIN-EQUAL`, `TRUE-LISTP`,
`UNION-EQUAL`, `SET-DIFFERENCE-EQUAL`, `SETP-EQUAL`, and
`NO-DUPLICATESP-EQUAL`, respectively.
