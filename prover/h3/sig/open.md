# H3 proof sessions

`(h3-api-open library)` returns a session for the given list of library
lines. A session is `(:h3-session base prefix measures)`. `base` is the
pair of an admitted Library and its prepared fact index, or an admission
failure. A nonempty `prefix` pairs the last successfully admitted list of
earlier lines with the Library and index for those lines. A nonempty
`measures` pairs the last definition's aid lines with the result of
parsing its measure records.

`(h3-api-prove-open session statement earlier aids)` returns
`(cons answer session2)`. `statement`, `earlier` and `aids` have the forms
specified by `h3-api-prove`. `answer` is the same value as for that
interface. The returned session belongs to the same library.

`(h3-api-prove-all library cases)` returns the answers in case order.
Each case is `(statement earlier aids)`. It opens the library once and
uses the returned session for the next case.
