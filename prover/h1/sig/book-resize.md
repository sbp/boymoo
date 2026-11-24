# List indexing and resizing proofs

`proof` is the H1 proof world used by the book tactics. Terms and Steps
have the forms in `prover/sig/proof.md`. Evidence Steps are used in list order.

| Call | Result | Failure |
|---|---|---|
| `(h1-book-resize-install-resize-bounds proof)` | The proof world with the index and resizing lemmas installed in order. | A failure from proof construction or registration. |
| `(h1-book-resize-show-spine proof test cons-step)` | A Step for the spine test or its negation, given cons or noncons evidence. | A failure from proof construction. |
| `(h1-book-resize-nth-branch proof index items cons-step zero-index)` | A Step opening `NTH` on the index and list terms with the spine and zero-index evidence Steps. | A failure from proof construction. |
| `(h1-book-resize-nth-on-cons proof index value test earlier-equation)` | A Step opening `NTH` on a cons term, with the list position restored by the earlier equation Step. `test` is the index evidence Step. | A failure from proof construction. |
| `(h1-book-resize-nf-nonnegative proof term)` | A Step proving the natural-number fixing of `term` nonnegative. | A failure from proof construction. |
| `(h1-book-resize-zero-is-inside proof index stop limit)` | A Step proving that the zero index is below the bound in Decrement `limit`, using the zero-index evidence Step `stop`. | A failure from proof construction. |
| `(h1-book-resize-decrement proof term active)` | A Decrement for a positive index term and its predecessor, with `active` the nonzero evidence Step. | A failure from proof construction. |
| `(h1-book-resize-align-index-bounds proof parent child numbers fixes)` | A Step equating the parent and child bounds with ordered type evidence `numbers` and fixing equations `fixes`. | A failure from proof construction. |
| `(h1-book-resize-out-of-range proof)` | A Step equating an out-of-bounds index to false. | A failure from proof construction. |
| `(h1-book-resize-resize-branch proof equation evidence)` | The resize equation Step with the branch selected by the supplied evidence Step. | A failure from proof construction. |
| `(h1-book-resize-resize-equation proof term)` | A Step unfolding the outer and inner resizing definitions. | A failure from proof construction. |
| `(h1-book-resize-resize-length proof)` | A Step proving the length of a resized list. | A failure from proof construction. |
| `(h1-book-resize-resize-nil proof)` | A Step proving that indexing outside a resized list yields false. | A failure from proof construction. |
| `(h1-book-resize-nth-resize proof)` | A Step for the indexing equation of a resized list. | A failure from proof construction. |
| `(h1-book-resize-nth-resize-nonempty holds proof cons-test before stop-index logical limit-bounds index-bounds limit active-index formula condition within-list successor-goals)` | `(cons step successor-goals)` with the branch Step and the given ordered substitution list extended by the branch's substitution. `holds` is a Boolean, `before` and `active-index` are Steps, the two bounds are Decrements, and the other named inputs are terms. | A failure from proof construction. |
| `(h1-book-resize-make-list-open proof)` | `(cons step proof)` with the opening Step and the world containing the auxiliary cons lemma. | A failure from proof construction or registration. |
| `(h1-book-resize-make-list-open-right evidence proof formula after)` | A Step rewriting the right side of the equation term `formula` by the selected branch of Step `after`, using the given evidence Step. | A failure from proof construction. |
| `(h1-book-resize-install-nth-zero-addition proof)` | The proof world with the lemma for adding zero to the index. | A failure if proof construction fails or the claimed equation differs. |
| `(h1-book-resize-nth-make-list proof)` | A Step for the indexing equation of a constructed list. | A failure from proof construction. |

A Decrement has the form `(:h1-decrement previous integral positive fixed previous-fixed)`.
`previous` is a term. The other fields are Steps for integrality,
positivity and the two fixing equations, in field order.
`h1-book-resize-make-decrement` takes the five fields in that order.
`h1-book-resize-decrement-previous`, `h1-book-resize-decrement-integral`,
`h1-book-resize-decrement-positive`, `h1-book-resize-decrement-fixed`
and `h1-book-resize-decrement-previous-fixed` each take a Decrement and
return its named field.

`*h1-book-resize-nth*`, `*h1-book-resize-length-limit*`,
`*h1-book-resize-resize*`, `*h1-book-resize-make-list*` and
`*h1-book-resize-tail*` are the prover symbols `COMMON-LISP::NTH`,
`ACL2::LIMIT`, `ACL2::RESIZE-LIST`, `ACL2::MAKE-LIST-AC` and
`ACL2::TAIL`. Substitutions retain binding order.
