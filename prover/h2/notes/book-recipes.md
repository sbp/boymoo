# Focused book dependencies

The focused recipes request BookProof operations through the protocol
in `prover/h2/sig/book-recipes.md`. The BookProof stores the rule selection
and fixed calls between operations. The `:search` dispatcher calls
tactics that take Search directly. The `:recipes` dispatcher installs
the returned Recipes before answering an optional folded induction request.

The character and list-count tactics can leave a request in the value
position of `(cons value search)`. Compression lookup uses its own
BookProof reply protocol to pass the current rewriting budget and Library.
