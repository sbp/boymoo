# T4 sessions

A session is a plain ACL2 value for one library. Callers obtain it from
`t4-api-open` or from the cdr of a `t4-api-prove-open` result.

| Call | Arguments and result |
|---|---|
| `(t4-api-open library)` | Prepare the list of library lines and return a session. A library preparation failure is recorded in the session. |
| `(t4-api-prove-open session statement earlier aids)` | Return `(cons answer session2)` for the statement string, the list of preceding line strings, and the list of aid line strings. `session2` is for the same library. |
| `(t4-api-prove-all library cases)` | Open one session for `library` and pass it through the list of `(statement earlier aids)` cases. Return the answers in input order. |

Each answer is the value of `t4-api-prove` on the same arguments.
An unsuccessful proof call gives `nil`.

The session retains the admitted context for the most recent earlier line
sequence that completed admission. A following extension admits only its
suffix. The session also retains the four most recently used aid sequences
that parsed successfully and their measure and hint dictionaries.
The most recent parsed statement can supply its fields and recursion
information when it occurs in the next suffix.
