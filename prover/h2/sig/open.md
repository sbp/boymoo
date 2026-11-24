# H2 library sessions

`(h2-api-open library)` prepares the library and returns a session.
`(h2-api-prove-open session statement earlier aids)` returns `(cons answer session2)`.
`(h2-api-prove-all library cases)` returns the answers to the ordered list of
`(statement earlier aids)` cases. The input lines and answer have the forms
specified in `prover/h2/sig/api.md`. Preparation failures are recorded in the
session. The proving interfaces handle failures in the same way as `h2-api-prove`.

`(h2-api-prove-all-loop library cases)` has the argument and answer format
of `h2-api-prove-all`.

A session has the form `(:h2-session base earlier context aids-cache)`. The
base and context each contain a BookProof, an index of normalized input
lines, and an index of reserved private names. The base is for the library
alone. The context is for the library and the last admitted earlier line
list. The aid cache holds a bounded list of aid arguments and their parsed
tables. All session fields are immutable ACL2 values.

The normalized line index associates each key with its parsed line record.
During a prefix change, the records for the preceding prefix can supply
parsed lines as the new prefix is admitted from the base.

A prepared context has the form `(:h2-session-context proof seen private trial)`.
The proof can carry the recursive call index and the ground Step described
in the Books and Search signatures. `trial` is `:unprepared` or the result
of preparing a proof trial for those inputs. A library preparation failure
occupies the base and context fields in place of a prepared context.
