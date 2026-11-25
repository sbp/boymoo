# Record laws

The Library and Step representations are specified in `prover/sig/library.md`
and `prover/sig/proof.md`. A formula is a prover term.

| Call | Result |
|---|---|

A call returns `(cons result library)`, a failure, or a request as specified
in `prover/t4/sig/constructors.md`. Both recipes may request
`:use-arithmetic`, with no operation arguments and `nil` as its
successful value. A successful result includes additions to the Library.

The record sufficiency tactic also requests `:boolean-true` with one proof
of an equality. Its value is the Step equating the equality to quoted T.

The `-with-library` forms of both calls take the same arguments and
retain the Library when a caller catches a failure, as specified in
`prover/t4/sig/constructors.md`.
