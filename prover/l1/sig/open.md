# L1 library sessions

| Call | Arguments and result |
|---|---|
| `(l1-api-open library)` | Takes a list of library lines and returns a session for those lines. |
| `(l1-api-prove-open session statement earlier aids)` | Takes a session, a statement line, a list of earlier lines and a list of aid lines. Returns `(cons answer session2)`, with the answer specified by `l1-api-prove` and a session for the same library. |
| `(l1-api-prove-all library cases)` | Takes a list of library lines and a list of `(statement earlier aids)` cases. Returns the answers in input order. |

A session is an ordinary ACL2 value. Use the three entry points to construct and pass it. With the same library and inputs, `l1-api-prove-open` returns the answer specified by `l1-api-prove`.
