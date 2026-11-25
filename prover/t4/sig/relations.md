# Paired list relations

A Library, a Step and a term have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. `*t4-relations-booleanp*` is the symbol for
`ACL2::BOOLEANP`. The order of the induction bindings is the order of first
occurrence on the traversal through the premises. The map of known shapes uses
the order in which the traversal learns the shapes.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t4-relations-paired-view lib call)` | Library and a term. The Step for opening a paired list relation, or `nil` when its definition does not have that form. | A failure from opening the relation or inspecting its body. |
| `(t4-relations-paired-branch lib opening left right)` | Library, the opening Step, a Step for the left shape and a Step for the right shape or `nil`. The equality Step for the selected branch. | A failure from constructing the Step or inspecting the shapes. |
| `(t4-relations-paired-boolean lib formula opening)` | Library, Boolean-valuedness claim and relation opening Step. The induction Step. | A failure from constructing the Step, including a failure for a non-Boolean returned value. |

A failure is the entire result. The two tactics that consult admitted laws
also have query entry points for dispatch through the library's fact search.

`(t4-relations-list-equivalence-query lib formula replies)` and
`(t4-relations-equivalence-conjunction-query lib formula replies)` use the
request protocol in `prover/t4/sig/constructors.md`. Both may request
`:fact-proof` with a term and an Evidence object. The forms without
`replies` start the query with an empty reply list.

The results book uses the following helpers with the same protocol.
A context is `(cons library replies)`, where `replies` is the unconsumed
suffix of the reply list.

- `(t4-relations-recipe-request context operation arguments)` consumes
  one reply and returns `(cons value new-context)`, returns a request if
  the reply list is empty, or propagates the failure in the reply.
- `(t4-relations-recipe-result result)` converts a pair of a value and a
  context into a pair of a value and a Library. A request or failure is
  returned as received.
- `(t4-relations-with-results ((name form) ...) result)` evaluates the
  forms in binding order and propagates a request or a failure.
- `(t4-relations-step-right step)` reads the right side of the equality
  in the first literal. It can return a failure from reading the Step.
- `(t4-relations-by-value-if proof value template yes no)` joins the Steps
  for the true and false branches of conditional term `value`. The
  `proof` argument is a Proof and `template` uses `*proof-result*`.
  It can return a failure.
- `(t4-relations-by-value-rewrite proof step equality template)` rewrites
  the Step with the reverse of the equality in the slot of `template`.
  It can return a failure.
- `(t4-relations-substitution bindings)` converts binding pairs
  `(variable term)` to an association list keyed by variable.

`(t4-relations-query recipe lib formula replies)` selects one of the query
entry points by keyword. The keywords are `:list-equivalence` and
`:equivalence-conjunction`.
