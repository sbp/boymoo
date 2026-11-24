# B1 library sessions

The statement, earlier lines, library and aids have the forms specified
in `prover/b1/sig/api.md`. Each case is a list `(statement earlier aids)`.

| ACL2 call | Result |
|---|---|
| `(b1-api-open library)` | A session for the supplied library. |
| `(b1-api-prove-open session statement earlier aids)` | `(cons answer session)` with any completed preparations retained in the returned session. |
| `(b1-api-prove-all library cases)` | The answers in case order, with one session passed between calls. |

A session is a plain ACL2 value. Pass a value returned by `b1-api-open`
or the session returned in the cdr of `b1-api-prove-open`. An answer is
the value of `b1-api-prove` on the same input lines. An unsuccessful
obligation gives `nil`.

The session has the form
`(:b1-session given library-lines prefixes measures history statement)`.
`given` is the prepared library Context or a failure encountered while
preparing it. `library-lines` is a search tree of pairs from distinct
raw library lines to their parsed fields. The Context's seen list is
reserved for earlier lines. `prefixes` maps exact earlier prefixes to
their Contexts and parsed lines. `measures` maps aid lists to measure
alists. `history` records the most recent successful earlier context's
boundary, parsed prefix and parsed suffix. `statement` is the last
successfully parsed statement, available when that line enters the history.
