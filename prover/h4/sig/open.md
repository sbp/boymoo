# H4 sessions

A session is a plain ACL2 value. Its fields belong to `open.lisp`.

| Call | Arguments and result |
|---|---|
| `(h4-api-open library)` | Takes the library lines in the form accepted by `h4-api-prove`. Returns a session for those lines. |
| `(h4-api-prove-open session statement earlier aids)` | Takes a session and the other inputs of `h4-api-prove`. Returns `(cons answer session2)`, where `answer` is the value of `h4-api-prove` for the session's library and `session2` is a session for that library. |
| `(h4-api-prove-all library cases)` | Takes a library and an ordered list of `(statement earlier aids)` triples. Returns the answers in that order. |

An input error produces the same answer as in `h4-api-prove`. A session can retain a failed preparation for reuse.
