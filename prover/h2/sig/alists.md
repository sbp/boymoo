# Association-list proofs

`p` is a Library from `prover/sig/library.md`. Terms and Steps use the
forms in `prover/sig/proof.md`. The theorem and fact `name` arguments are
strings without a package qualification.

| ACL2 call | Result | Failure |
|---|---|---|
| `(h2-alists-distinguish p term present absent)` | A Step that disproves equality `term` using the predicate Steps `present` and `absent`. | A failure from proof construction. |
| `(h2-alists-heading-facts p replies)` | `(cons names p)` with the five heading fact name strings, in source order, and the updated Library. | A failure from proof construction or derivation. |
| `(h2-alists-array-extension p formula replies)` | `(cons step p)` for the array extension term `formula`. | A failure from proof construction or derivation, or a failure from a malformed formula. |
| `(h2-alists-ordered-alist p replies)` | `(cons name p)` for the implication from `ORDERED-SYMBOL-ALISTP` to `ALISTP`, with the auxiliary fact name as a string. | A failure from proof construction or derivation. |
| `(h2-alists-first-key alist)` | The term `(CAR (CAR alist))`. | None. |
| `(h2-alists-ordered-projections p replies)` | `(cons names p)` with the tail, head pair, head symbol and neighbor fact names as strings, in that order. | A failure from proof construction or derivation. |
| `(h2-alists-normalized-fact p name)` | `(cons name p)` with the logical fact name as a string and the updated Library. If there are no wrappers to remove, the result uses the supplied name. | A failure from proof construction. |
| `(h2-alists-ordered-changes p theorem formula replies)` | `(cons step p)` for the ordered alist operation named by theorem string `theorem`. | A failure from proof construction or derivation. |
| `(h2-alists-channel-headers p formula replies)` | `(cons step p)` for the input or output channel header theorem `formula`. | A failure from proof construction or derivation. |
| `(h2-alists-assoc-after-add p theorem formula replies)` | `(cons step p)` for the association or bound theorem named by `theorem`. | A failure from proof construction or derivation. |

The constants `*h2-alists-alistp*`, `*h2-alists-assoc*`, `*h2-alists-listp*`,
`*h2-alists-ordered*`, `*h2-alists-symbol-lt*` and `*h2-alists-symbolp*` are
the corresponding symbol terms. `*h2-alists-header*` is the quoted
`:HEADER` term.

## Derivation requests

The ordered list `replies` supplies results of `h2-recipes-recipes-derive`,
with one `(cons step p)` or failure per call. With a reply missing, the result is
`(cons request p)` with the Library at the point of the call. The predicate
`h2-alists-request-p` recognizes `request`, and
`h2-alists-request-arguments` returns its arguments in order:
`(formula definitions facts variable depth repeat seeds cases split-limit)`.
`definitions` and `repeat` are space-separated name strings, `facts` is
an ordered list of fact names, and `variable` is a name string or `nil`.
Call the derivation with those arguments and the supplied Library, append
its result to `replies`, and call the original function again with its
original Library. Carry the caller's proof search configuration between
requests. A failure is returned as the entire result.

## Derivation helpers

Intermediate results use `(value p remaining-replies)`. A missing reply
puts the request in the value field. A failure is the entire result.

| ACL2 call | Result | Failure |
|---|---|---|
| `(h2-alists-derivation-result value p replies)` | The intermediate result with `value`, the Library `p` and the supplied remaining replies. | A failure supplied as `value`. |
| `(h2-alists-with-derivations p replies ((name form) ...) result)` | A binding macro that evaluates each `form` in order and binds `name`, `p` and `replies` from its intermediate result before evaluating the next form or `result`. A request or failure returns immediately. | A failure from a form or the `result` expression. |
| `(h2-alists-finish-derivations result)` | The public `(cons value p)` result from the intermediate result. | A failure supplied as `result`. |
| `(h2-alists-has-fact p name)` | True when the Library has the `ACL2` symbol named by the string `name` as a fact. | None. |
| `(h2-alists-auxiliary p replies name formula definitions facts variable cases split-limit)` | The intermediate result for the auxiliary fact. The name string omits `SELF-H2-`. Other arguments follow the derivation request protocol. | A failure from derivation or proof construction. |
| `(h2-alists-logical-result equality)` | The right operand of the first literal of the equality Step. | Failure when the Step is absent or its literal cannot be read. |
