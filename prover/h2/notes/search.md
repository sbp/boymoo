# Search requests and results

A Search request supplies its Library, rule configuration, and
inherited operation arguments. `h2-search-search-call-with-remainder`
provides the unused replies on success.
`h2-search-search-call-with-outcome` also preserves them when the call
returns a failure. A recipe can continue with the resulting Search
after handling the value. See `prover/h2/sig/search.md`.
