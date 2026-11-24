# T3 library sessions

Opening a session admits the given library and applies the applicable
helper recipes. It then builds the theorem's fact and rewrite indexes,
a line index, and recursive-call summaries. The ground proof context
comes from the book's constant.

The session holds one earlier prefix. When the next prefix extends it
exactly, the session admits only the unseen lines in the suffix. A
different prefix uses the prepared library as its starting scope. The
line index can supply the parsed form of a line from the preceding
scope, and the latest parsed statement is available for admission into
the next prefix. The session keeps up to four aid maps keyed by their
complete ordered line sequences.

`t3-api-prove-all` passes the resulting session from each case to the
next. The test of the set is `sh prover/t3/test.sh`.
