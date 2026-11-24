# T2 library sessions

| Call | Arguments and result | Failure |
|---|---|---|
| `(t2-api-open library)` | An opaque session for the given library. The library is a list of source lines, `nil`, or one string containing the lines. | None. |
| `(t2-api-prove-open session statement earlier aids)` | `(cons answer session2)`, where `answer` is the value of `t2-api-prove` on the same inputs and `session2` is a session of the same library. | As in `t2-api-prove`, a failed proof attempt gives a `nil` answer. |
| `(t2-api-prove-all library cases)` | The list of answers for `cases` in order, using one session. Each case is `(statement earlier aids)`, with input forms as in `prover/t2/sig/api.md`. | As in `t2-api-prove`, a failed proof attempt gives a `nil` answer. |
