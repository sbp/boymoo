# Witness candidates

A term and a symbol use the forms in `prover/sig/proof.md`. The `formulas`
argument is a list of `(name formula)` pairs in constraint order. A function
name map is an insertion-ordered alist with `(name . replacement)` entries.

| Function | Arguments in order | Result | Failure |
|---|---|---|---|
| `h2-witnesses-rename-functions` | Term, function name map | Term with function heads renamed, including the bodies of applied lambdas | Failure for a missing compound term field. |
| `h2-witnesses-definitions-in` | Formula | List of oriented equation pairs in traversal order | Failure for a missing formula field. |
| `h2-witnesses-possible-bodies` | Function name, arity, `formulas`, map of unknown names to their witnesses | Distinct `(formals body)` pairs in first-insertion order, followed by the fallback candidates in order when new | A failure from reading or renaming a formula. |
| `h2-witnesses-witness-formals` | Integer arity | List of `H2-ARG-i` symbols with indices from 1 through the arity | None. |
| `h2-witnesses-prove-witness` | H2 proof search object, `(functions formulas)` constraint data, reply list described below | `(cons entry proof)` with the witness proof entry and the resulting proof object, or a request for a caller operation | `Unproved` if no candidate closes the constraint, or a failure from proof construction. |

`functions` is a list of `(name arity)` pairs. The proof checks the all-false
and all-true assignments, then the product of the candidate lists. The
assignment limit is applied before and after removing duplicate assignments.

The result `(:h2-witnesses-request operation proof args)` names a caller
operation. Its arguments are available through `h2-witnesses-request-operation`,
`h2-witnesses-request-proof`, and `h2-witnesses-request-args` in field order.
`h2-witnesses-request-p` recognizes the request. Begin with `nil` replies and
append each reply to the end of the list before repeating the call with its
original proof and data. Operations are `:calls-in` (one goal, returning its
calls in traversal order), `:configure-book` (the list of definitions to open,
with the dynamic rule flag set to `t`, returning the configured proof), and `:solve` (one goal,
returning `(cons step proof)`). A failed solve can reply with
`(cons failure proof)` to retain the proof as of the failure; an uncaught failure
is the entire result. These calls leave the book-specific operations with
the caller while the witness book controls the assignment order.

The symbol constants are `*h2-witnesses-iff*` and `*h2-witnesses-implies*`.

The proof passed to the witness book is the inherited Search or its Library.
Set the enclosing BookProof's arithmetic field to false when entering the
assignment search. The `:configure-book` argument list is `(definitions t)`.
Use the default empty repeat and fact lists. The `:solve` argument list is
`(goal rewriting-budget)` with a budget of 2500. Keep the BookProof fields
between requests and use the Search from the current request as its inherited
Search. When an assignment fails, the witness book truncates entries and
deletes witness facts and definitions before the next request.

`h2-witnesses-prepare` takes constraint data and returns an ordered witness
plan or a failure from reading it. It computes the witness name digest.
`h2-witnesses-plan-names` returns the ordered witness symbols from a plan.
`h2-witnesses-prove-prepared` takes the original Search, a prepared plan and
the ordered replies. Its result has the same form as `prove-witness`. The
same plan supplies all requests for one witness search, so the digest and
candidate lists are computed once for that search.

| Supporting call | Arguments in order | Result and failures |
|---|---|---|
| `h2-witnesses-pair` | Sequence to unpack | Its two elements, or a failure from unpacking it. |
| `h2-witnesses-names` | Function pairs, uppercase digest string, starting index | Witness symbols in function order. The function returns the symbols on these inputs. |
| `h2-witnesses-replacements` | Function pairs, witness symbols, initial function name map | The map updated in zip order, or a failure from unpacking a function pair. |
| `h2-witnesses-candidates` | Function pairs, formulas, replacement map | The candidate lists in function order, or a failure from reading a pair or formula. |
| `h2-witnesses-goals` | Formulas, replacement map | The renamed formulas in constraint order, or a failure from renaming. |
| `h2-witnesses-assignments` | Function pairs, candidate lists | The capped list of distinct assignments in search order. The function returns the symbols on these inputs. |
| `h2-witnesses-prove-assignments` | Proof, ordered candidate assignments, ordered goals, root symbol, witness symbols, initial entry count, replies | The same result or request as `prove-witness`, or a failure from trying an assignment. |
| `h2-witnesses-rollback` | Proof, witness symbols, initial entry count | Proof with entries truncated to that count and the witness definitions and facts deleted. The function returns the symbols on these inputs. |
