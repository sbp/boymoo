# Multiple-value results

A Library, a Step and a term have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. These are the names of the symbol constants.

| ACL2 constant | Symbol |
|---|---|
| `*t4-results-mv-nth*` | `ACL2::MV-NTH` |
| `*t4-results-zp*` | `ACL2::ZP` |
| `*t4-results-nth*` | `COMMON-LISP::NTH` |
| `*t4-results-endp*` | `COMMON-LISP::ENDP` |
| `*t4-results-atom*` | `COMMON-LISP::ATOM` |
| `*t4-results-true-list*` | `ACL2::TRUE-LISTP` |
| `*t4-results-result-predicates*` | Set of `ACL2::BOOLEANP`, `TRUE-LISTP`, `SYMBOL-LISTP`, `ALISTP`, `CHARACTER-LISTP`, `NAT-LISTP` and `INTEGER-LISTP`, listed by their S-expression text. |

`lib` is a Library. `recursive` is the set of names of recursive definitions
as a list. It is used for membership tests. The substitution lists for
induction and the maps of called applications follow the first occurrence
order of the recursive calls, with substitutions for each call in argument
order. For result-path search, then-branches precede else-branches, and
distinct projected calls retain the order of their first occurrence.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t4-results-true-list-cons lib pair)` | Library and a `CONS` term. An equality Step reducing its proper-list test to the test of its tail. | A failure from constructing the Step. |
| `(t4-results-projection lib term)` | Library and term. A pair of a field-selection equality Step or `nil` and the Library with the corresponding auxiliary lemma if needed. | A failure from constructing the Step or reading the field. |
| `(t4-results-unfold-projection lib term)` | Library and a call of `MV-NTH` or `NTH` on a `CONS` term at a quoted integer index. The equality Step produced by unfolding the projection. | A failure from constructing the Step. |
| `(t4-results-result-property lib formula)` | Library and claim term. A pair of the Step or `nil` and the resulting Library. | A failure from proof search or the result-path limit. |
| `(t4-results-list-projection-invariant lib formula recursive)` | Library, claim term and recursive name set. A pair of the induction Step or `nil` and the resulting Library. | A failure from constructing the Step or from a missing proper-list premise. |
| `(t4-results-guarded-result-type lib formula recursive)` | Library, claim term and recursive name set. A pair of the Step or `nil` and the resulting Library. | A failure from constructing the Step, from a missing type premise, or from the result-path limit. |
| `(t4-results-list-result-invariant lib formula recursive)` | Library, claim term and recursive name set. A pair of the induction Step or `nil` and the resulting Library. | A failure from proof search or constructing the Step. |

A failure is the entire result. Tactics that need the library's proof search
also have query entry points. A caller that holds a subclass uses its
Library component, retaining the returned Library even when the Step is
`nil`.

The search entry points with replies are
`(t4-results-result-property-query lib formula replies)`,
`(t4-results-list-projection-invariant-query lib formula recursive replies)`,
`(t4-results-guarded-result-type-query lib formula recursive replies)`,
and `(t4-results-list-result-invariant-query lib formula recursive replies)`.
The forms without `replies` start the query with an empty reply list. Pass
the original arguments and append replies in evaluation order as in
`prover/t4/sig/constructors.md`. The `:solve` operation takes the formula,
the signed tests, the list of extra Steps and the depth, in that order.
Its successful value is a Step. The other operations and replies have the
forms in the constructor signature.

`(t4-results-query recipe lib formula recursive replies)` selects a search
entry point by keyword. The keywords are `:result-property`,
`:list-projection-invariant`, `:guarded-result-type` and
`:list-result-invariant`. The result property recipe uses the defined
calls in the formula and does not use the recursive name set.

`(t4-results-unfold-projection-with-library lib term packages)` returns
`(cons step lib)` or a failure. Use this form to retain a Boolean-value lemma
added while testing the constructed list. `packages` is the list of known
package names as strings, used when computing quoted symbol metadata.
`(t4-results-projection-with-packages lib term packages)` takes the same
package list and otherwise has the result of `t4-results-projection`.
The forms without a package list use the initial ACL2, Common Lisp and
keyword packages.

The guarded result recipe requests `:prove` with the goal, premises and
definitions to unfold. The reply value is the Step. The predicate names
have the same order as `*t4-results-result-predicates*` in the list of
definitions. Simplification uses that list for membership.

For the `:list-projection-invariant` recipe, `t4-results-query` can return
`(cons failure lib)` when a later branch fails after an auxiliary lemma
has been admitted. BookLogic retains that Library when it catches the
failure. The named invariant function and its `-query` form return the
failure directly.
