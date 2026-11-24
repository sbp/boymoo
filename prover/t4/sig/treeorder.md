# Tree order proofs

`lib` is a Library as specified in `prover/sig/library.md`. Terms and Steps
have the forms in `prover/sig/proof.md`. `recursive` is the set of recursive
function names, represented by the list of symbols in S-expression order. The
proofs use that list for membership.

| Call | Arguments and result |
|---|---|
| `(t4-treeorder-tree-order-equivalence lib formula recursive replies)` | Library, equality claim, recursive names and method replies. Returns the proof of equality with `LEXORDER`, or `nil` in the value position when the tactic does not apply. |
| `(t4-treeorder-strict-tree-order lib formula recursive replies)` | Library, equality claim, recursive names and method replies. Returns the proof of the strict tree order specification, or `nil` in the value position when the tactic does not apply. |

Both tactics return `(cons value lib)` on completion, carrying the Library
with any entries added by the tactic, or a failure or request as the entire
result. A failure can arise while reading a term or constructing a proof.

## Inherited book methods

`replies` is the ordered list of replies for this invocation, beginning
with `nil`. The request accessors each take the entire result and do not return a failure. `t4-treeorder-request-p` recognizes a request.
`t4-treeorder-request-method`, `t4-treeorder-request-args` and
`t4-treeorder-request-lib` give its keyword, ordered argument list and
Library at the request.

| Method | Arguments and value |
|---|---|
| `:use-arithmetic` | No arguments. The callback runs the book's arithmetic setup and returns `nil` in the value position. |
| `:fact-proof` | Term and extra Steps in evidence order. The callback constructs Evidence with no signed tests and these extra Steps and asks the book for its fact proof. The value is a Step or `nil`. |

Supply `(cons value lib)` for each reply, with the Library after the
method, or supply the method's failure. Append the reply and call the tactic
again on the original arguments. Each invocation, including one returning
`nil`, occupies one position in the reply list.

Two further methods use the same reply form. `:fact-proof-evidence` takes a
term and the Evidence object from `prover/t4/sig/structural.md`, including
the findings from earlier type queries in that branch. Its value is the
Step or `nil` from the book's fact lookup. `:boolean-true` takes one Step
proving an equality. Its value is the book's Step equating that equality
to quoted `T`.

`recursive` may also be supplied in the insertion order used by BookLogic.

A `:constant` request takes one term whose arguments are quoted. It
uses BookLogic's constant method for operations beyond the Ordinals
constant rules. The value is the equality Step or `nil` when the
method leaves the term unchanged.
