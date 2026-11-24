# Derivation and replies

`h2-book-logic-derive` configures the Search and returns the updated
Search with the Step, failure, or inherited request. Division and
equivalence use the updated Search for successive derivations.
`h2-book-logic-set-rules` resolves the definition and repeat names and
keeps fact names in their supplied order.

`h2-book-logic-search-call` retains unused replies when a scoped
derivation returns a failure. A caller can then restore its fixed
calls with the resulting Search.
