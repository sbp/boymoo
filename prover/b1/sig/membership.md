# Membership

`lib` is a Library as specified in `prover/sig/library.md`, with the B1 proof
methods. Terms and Steps have the forms specified in `prover/sig/proof.md`.
Each function can return a failure in place of the entire result.

| ACL2 call | Arguments and result |
|---|---|
| `(b1-membership-member-nil lib formula)` | Step proving the negated membership formula for an empty list. |
| `(b1-membership-impossible-member lib assertion empty goal)` | Given a membership Step, an equality Step reducing its first literal to quoted `NIL`, and a goal term, return a Step for the goal under the resulting contradiction. |
| `(b1-membership-member-requires-cons lib formula)` | Step proving that successful membership implies the list is a cons. |
| `(b1-membership-member-from-tail lib formula)` | Step proving that membership in the tail implies membership in the list. |
| `(b1-membership-member-of-suffix lib formula)` | Step proving that membership in the suffix returned by another membership call implies membership in the original list. |
| `(b1-membership-member-contrapositive lib formula)` | Step proving the contrapositive of membership from a tail or membership suffix. |
| `(b1-membership-member-proper lib formula)` | Step proving that a membership call on a proper list returns a proper list. |
| `(b1-membership-list-fix-lemmas lib)` | Library with the properness and identity lemmas for `TRUE-LIST-FIX`, added in that order if absent. |
| `(b1-membership-member-of-fixed-list lib formula)` | `(cons step lib)` with the Step for the fixed-list membership equality and the Library containing the auxiliary lemmas. |
| `(b1-membership-membership-head-step lib formula)` | Step proving the membership equality with the tail under the given head mismatch. |
| `(b1-membership-singleton-member lib formula)` | Step proving the given membership equality for a singleton. |
| `(b1-membership-membership-case lib formula equations evidence induction)` | Step for `formula` from the lists of equality Steps and evidence Steps, both in supplied order. Pass `nil` for empty evidence or for the omitted induction Step. |
| `(b1-membership-member-of-fixed-list-iff lib formula)` | Step proving the membership equivalence before and after `TRUE-LIST-FIX`. |
| `(b1-membership-member-of-set-operation lib formula)` | Step proving the given membership equivalence for union, difference, removal, or duplicate removal, with its premise when present. |
| `(b1-membership-member-of-singleton-length lib formula)` | Step proving the given membership equivalence under the length-one hypothesis. |
| `(b1-membership-member-after-removal lib formula)` | Step proving that any member remaining after removing one occurrence was a member of the original list. |
| `(b1-membership-member-after-removal-iff lib formula)` | Step proving the given membership equivalence after removing one occurrence. |
| `(b1-membership-member-at-index lib formula)` | `(cons step lib)` with the Step proving that the bounded `NTH` selection is a member and the Library containing the auxiliary arithmetic lemmas. |

In `membership-case`, the alist of cons evidence is keyed by the
argument of each `CONSP` first literal. The last Step for a repeated key
is used. Derived evidence is appended in equation order to the supplied
evidence. Rewrite rules use the same equation order.

The constants `*b1-membership-true-listp*`, `*b1-membership-item*`,
`*b1-membership-union*`, `*b1-membership-difference*`,
`*b1-membership-remove*`, `*b1-membership-remove1*`,
`*b1-membership-deduplicate*`, and `*b1-membership-cons-hint*` are the
corresponding ACL2 term symbols.
