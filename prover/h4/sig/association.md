# Induction for association lookups

The Library, Proof, term and Step forms are those of the shared books.
These operations are available to the books that load before the H4
Tactics book. Each can return a failure.

| Call | Result |
|---|---|
| `(h4-association-arity-or-logic p formula)` | A Step for the arity or logic property carried by the association entry in the given term. The first argument is the Library. |
| `(h4-association-local-lemma p label step)` | `(cons name library)` with the resulting Library. The label is a prover symbol or a string to prefix with `H4-`. The fact and entry retain the clause of the Step in order. |
| `(h4-association-conjunction p formula first second)` | A Step for the conditional term formed from the first literals of the two Steps, with quoted NIL as its false branch. |
| `(h4-association-conjunct p step)` | A two-element list of the Steps for the conjuncts of the first literal. |
| `(h4-association-imply p formula conclusion)` | A Step for the implication term using a Step for its conclusion. |
| `(h4-association-modus-ponens p step evidence)` | A Step for the conclusion of the implication using a Step for its premise. |
| `(h4-association-nil-value p negative)` | A Step equating the negated proposition in the input Step to quoted NIL. |
| `(h4-association-normalize p term evidence expand rewrites)` | An equality Step for the normalized term. Evidence and rewrites are Step lists and expand is a list of definition names. Pass `nil` for an omitted list. |
| `(h4-association-establish p formula evidence expand rewrites)` | A Step establishing the term. The last three arguments are as in normalization. |
| `(h4-association-number p term evidence)` | A Step proving the term is an ACL2 number. Evidence is a list of integer Steps. |
| `(h4-association-rational p term evidence)` | A Step proving the term is rational. Evidence is a list of integer Steps. |

The proof rules select H4 propositional facts when they are present in
the Library. The normalization entry point uses the default provider.

`(h4-association-step-at step index)` reads the element at the natural
number index in the first literal of a Step. It may return a failure.
`(h4-association-case-of p formula test yes no)` combines the Steps
for `formula` under the true and false assumptions about `test`.
It may propagate a failure or return an assertion failure.
