# Compression lookup

The lookup recipes request `:compression-lookup-theorem` and
`:compressed-aref` through BookProof. Their other operations install a
Library or set the rewriting budget. The inherited Search dispatcher
uses `h2-compression-lookup-search-call` to answer the lookup
operations listed in `prover/h2/sig/compression-lookup.md`.
