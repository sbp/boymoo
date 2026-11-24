# H1 sessions

A session is an ACL2 value passed from one proof request to the next. Its
contents are private to `open.lisp`.

| ACL2 call | Result |
|---|---|
| `(h1-api-open library)` | A session for the supplied library. |
| `(h1-api-prove-open session statement earlier aids)` | `(cons answer session2)`, where `answer` is the public proof result and `session2` is a session for the same library. |
| `(h1-api-prove-all library cases)` | Answers in case order, using one session. Each case is `(statement earlier aids)`. |

Input lines and the proof result have the forms specified in `api.md`.
A library preparation failure is recorded in its session. Proof requests
with that session return `nil`.
