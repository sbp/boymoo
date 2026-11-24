# T1 library sessions

A session is an ACL2 value returned by `api-open` or by the cdr of
`api-prove-open`. Its representation is private to `open.lisp`.
The input groups have the same forms as in `prover/sig/api.md`.

| Function | Arguments | Result |
|---|---|---|
| `api-open` | `library`, the input library lines | A session for that library. Any preparation error is retained in the session. |
| `api-prove-open` | `session`, `statement`, `earlier`, `aids` | The pair `(cons answer session2)`. The car is the result of `api-prove` on the session's library. The cdr is a session for the same library. |
| `api-prove-all` | `library`, `cases`, a list of `(statement earlier aids)` | The list of answers in case order. |

An unsuccessful proof attempt or input failure gives `nil` in the
answer position.
