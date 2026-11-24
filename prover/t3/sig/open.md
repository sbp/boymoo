# T3 sessions

| Call | Arguments and result | Failure |
|---|---|---|
| `(t3-api-open library)` | A given library in the line-sequence form of `t3-api-prove`. Returns a session for that library. | None. |
| `(t3-api-prove-open session statement earlier aids)` | A session, a statement line, the complete earlier line sequence and the aid line sequence. Returns `(cons answer session)` with the answer of `t3-api-prove` and the updated session of the same library. | None. |
| `(t3-api-prove-all library cases)` | A given library and a list of `(statement earlier aids)` cases. Returns the answers in order, passing the session from one case to the next. | None on these forms. |

A session is a plain ACL2 value. Its base scope contains the admitted
library, the theorem indexes and a membership index of admitted lines.
The session keeps the scope of one earlier prefix and the exact supplied
lines of that prefix. The base supplies the initial scope when a case
has a different prefix. The session keeps up to four parsed aid maps,
keyed by their ordered line sequences. Proof attempts leave scope data
available to subsequent calls.

The membership index maps each normalized source line to its parsed
line. The session also keeps the most recently parsed statement so
its parsed form is available when it enters the next prefix. The
prepared theorem indexes carry the recursive calls and changing
argument indices of the definitions in scope.

The session has the form `(:t3-api-session base current earlier measures recent)`.
Each scope pairs the theorem search with its line index. If library preparation
fails, both scope fields hold the failure and the session returns `nil` answers.
