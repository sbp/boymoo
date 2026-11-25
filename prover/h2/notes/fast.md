# H2 search and prefix indexes

`h2-books-run-indexed-search` prepares an index of facts for solving and
induction. The ordinary Search and Context constructors support ordered
lists. The indexed Context keeps those lists for established literals and
split tests. Rule completion visits the candidates in each bucket in their
stored order, and split selection visits the same ordered tests.

| Table | Key | Indexed use |
|---|---|---|
| Reductions | `(term opened active)` | A balanced tree holds an equality Step or `nil`. A present `nil` records a query in progress or a completed query with no equality. |
| Deductions | `(term active)` | A balanced tree holds a Step or `nil`. Lookup distinguishes a present `nil` from an absent key. |
| Representatives | The representative of an oriented equality | A balanced tree provides membership of the full term. |
| Learned literals | A literal in the current learning call | A balanced tree provides membership for Search and the BookProof hook. |
| Facts used to instantiate rules | The fact name | A balanced tree indexes the active Proof's clauses. Rule construction and iteration read the ordered Proof fields. |
| Written names | The escaped certificate name | The direct and session interfaces use a balanced tree for an admission of at least 32 lines. Traversal by key gives the BookProof's order when admission completes. |

The trees use `equal` for identity, ACL2's lexicographic order for terms,
and `string<` for strings. Adding a literal clears both query tables.
Replacing the Library invalidates the fact index. `h2-search-indexed-fact`
instantiates the resulting Step from the active Proof.
`h2-books-run-indexed-search` removes the fact index when returning
the BookProof.

## Inherited search calls

A request suspends the current invocation at an inherited operation.
The caller supplies the reply in evaluation order. The reply transcript
records completed subcalls as values, so replay can continue to the next
request while preserving the visits, decisions, hook replies, and fuel
charges of the invocation. The ordered reply interface also accepts
explicit replies.

