# Association list proofs

Terms, Steps and Libraries have the forms in `prover/sig/proof.md` and
`prover/sig/library.md`. `p` is the Library used by H4 tactics. The constants
`*h4-book-alists-lookup*`, `*h4-book-alists-key-equal*`,
`*h4-book-alists-remove*`, `*h4-book-alists-fork*` and
`*h4-book-alists-lookup-after-removal*` are prover symbols.

| ACL2 call | Result | Failure |
|---|---|---|
| `(h4-book-alists-keyed-removal formula)` | Whether a term contains `HONS-REMOVE-ASSOC` and either `HONS-ASSOC-EQUAL` or `FAST-ALIST-FORK`. | A failure from walking the term. |

A KeySearch uses the BookSearch state and its ordinary constructor. Its
specialized methods use that state with the same interpretation as the base
methods. `evidence` is a dictionary from first literals to Steps, kept in
insertion order. New keys append entries. Setting an existing key takes the
place of its existing value. `premises` is a list of Steps in the order given
to the search. `rule` is a BookSearch rule, `depth` is the remaining fact
search depth, and `rewrite` is `t` when matching the left side of an equation.

| ACL2 call | Result | Failure |
|---|---|---|
| `(h4-book-alists-key-search-key-aliases search evidence)` | The oriented equations, in evidence order. | A failure from reading or orienting an equation. |
| `(h4-book-alists-key-search-substitute-keys search evidence)` | Evidence with its additional key substitutions. | A failure from constructing a substitution. |
| `(h4-book-alists-key-search-expose-removal search term)` | A Step opening a selector of a constructor or a removal call on a constructor, or `nil`. | A failure from reading or opening the term. |
| `(h4-book-alists-key-search-selected-equations search evidence)` | Steps selected and rewritten in evidence order. | A failure from reading or constructing a Step. |
| `(h4-book-alists-key-search-join-equalities search evidence)` | Evidence with the additional equations formed from Steps with a common side. | A failure from constructing an equation. |
| `(h4-book-alists-key-search-hypotheses search premises)` | The ordered evidence dictionary with the specialized additions. | A failure from collecting the evidence. |

`instantiate` returns `(cons result search)` as in `book-tactics.md`. A
matching direct replay leaves the ordinary instantiation budget unchanged.
During induction, the search requests an evidence map for each premise list
and replays the removal rewrite before applying the ordinary rewrite filters.
Replay may itself spend budget when it uses search to discharge a premise.
