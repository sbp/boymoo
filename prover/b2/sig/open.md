# B2 proof sessions

A session is a plain ACL2 value scoped to one library. Pass it to the proof
interface as an opaque value. `library`, `statement`, `earlier`, and `aids`
have the same forms as in `prover/b2/sig/api.md`.

| Call | Result |
|---|---|
| `(b2-api-open library)` | A session for the given library. |
| `(b2-api-prove-open session statement earlier aids)` | `(cons answer session2)`. `answer` is the value of `b2-api-prove` for these arguments and the session's library. `session2` retains preparation for the same library. |
| `(b2-api-prove-all library cases)` | The list of answers in case order. Each case is `(statement earlier aids)`. |

Library and proof preparation failures have the same public result as through
`b2-api-prove`.
