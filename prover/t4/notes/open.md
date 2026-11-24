# Library sessions

`t4-api-open` prepares the ground and admitted library Proof, the
BookLogic indexes, the choice rules in admission order, and a balanced
lookup tree of distinct normalized library lines. Each distinct line is parsed
once for admission and registration. The resulting context includes
the proof indexes, evaluator tables, package and recursion information,
and sizes of admitted definition bodies.

`t4-api-prove-open` uses the lookup tree for duplicate checks. A session
retains the most recent admitted earlier-line prefix and its raw input
sequence. A matching extension admits only the suffix. A shorter or
different sequence starts at the library context. The remembered prefix
is the context before proof search, so lemmas generated during a proof
attempt belong to that attempt.

The session retains the most recent parsed statement and the four
most recently used aid sequences that parsed successfully. Transient
search terms are sized as needed. A retained size applies when the
definition body matches. Proof Steps generated during search stay
with their proof attempt.

`t4-api-prove-all` opens one session and passes each resulting session
to the next case. The driver uses `t4-api-open` and `t4-api-prove-open`
over whole books, one session a book (`prover/OPEN.md`, "The test"). The test of the set is `sh prover/t4/test.sh`.
