# Partition, merge, and sort

A Library and a Step have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. Terms and names are prover data. Evidence maps are
insertion-ordered association lists from terms to Steps. Rules are an ordered
list of equality Steps.

| Call | Result | Failure |
|---|---|---|
| `(b2-sorting-bit item lst)` | The Boolean membership term for item term `item` and list term `lst`. | — |
| `(b2-sorting-either terms)` | The right-associated conditional disjunction of the terms in list order. | Empty term list. |
| `(b2-sorting-length lst)` | The `LEN` call on list term `lst`. | — |
| `(b2-sorting-apply-equations library formula rules)` | The equality Step for rewriting `formula` with `rules`, in rule order and then in argument traversal order. | Failure from reading a Step or constructing the proof. |
| `(b2-sorting-boolean-equality library formula rules)` | A Step proving equality term `formula` using `rules`. Pass `nil` for the default rules. | Failure from reading a term or constructing the proof. |
| `(b2-sorting-member-view library item lst premise)` | A Step opening Boolean membership of `item` in `lst` under the cons or atom Step `premise`. | Failure from proof construction. |
| `(b2-sorting-member-cons library item pair)` | A Step opening Boolean membership of `item` in the cons term `pair`. | Failure from proof construction. |
| `(b2-sorting-partition-length library)` | `(cons name library)` with the length lemma's name and the Library containing it. | Failure from proof construction. |
| `(b2-sorting-partition library)` | `(cons (list size elements) library)` with the length and membership lemma names, respectively, and the Library containing them. | Failure from proof construction. |
| `(b2-sorting-reverse-append library)` | `(cons name library)` with the reverse-append membership lemma's name and the Library containing it. | Failure from proof construction. |
| `(b2-sorting-merge-membership library)` | `(cons name library)` with the merge membership lemma's name and the Library containing it. | Failure from proof construction. |
| `(b2-sorting-merge-descent library arguments measure known)` | An ordinal decrease Step. `arguments` is the ordered list of recursive actuals, `measure` is the parent measure term, and `known` is an evidence map. | Failure from proof construction or a missing key in `known`. |
| `(b2-sorting-nontrivial-partition library size nonempty-tail)` | A two-element list of the ordinal decrease Steps for the even and odd parts, respectively. `size` is the length lemma name and `nonempty-tail` is the Step proving the tail of `X` is a cons. | Failure from proof construction. |
| `(b2-sorting-merge-sort-membership library formula)` | `(cons step library)` with the proof Step for theorem term `formula` and the Library extended by its definition and lemmas. | Failure from proof construction. |
| `(b2-sorting-sort-wrapper library name formula)` | A proof Step for the named wrapper theorem with statement `formula`. | Failure from proof construction. |

For a call that returns a pair, a failure is the entire result.

The symbol constants are `*b2-sorting-sort*` (`SORT-SYMBOL-LISTP`),
`*b2-sorting-merge*` (`STRICT-MERGE-SYMBOL<`), `*b2-sorting-merge-sort*`
(`STRICT-MERGE-SORT-SYMBOL<`), `*b2-sorting-evens*` (`EVENS`),
`*b2-sorting-odds*` (`ODDS`), `*b2-sorting-member*` (`MEMBER-EQUAL`),
`*b2-sorting-revappend*` (`COMMON-LISP::REVAPPEND`), `*b2-sorting-bit*`
(`B2-MEMBER-BOOLEAN`), and `*b2-sorting-item*` (`A`).
