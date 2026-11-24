# H3 library sessions

`h3-api-open` admits the library and prepares the fallback index once.
The index groups facts by the heads of formulas, conclusions, and
left-hand sides of equations. The index records each fact's insertion
position. A later declaration of that fact can replace its contribution
while keeping its position.
A tactic that needs an index receives the earliest outstanding failure
from indexing a malformed fact.

The session keeps the last admitted earlier lines, their Library and
index, and one aid list with its parsed measure records. Equal earlier
lines reuse the admitted Library. An extension admits and indexes
only the suffix. A different or shorter list uses the prepared library
as its starting point.

The prefix retains the declarations even when a tactic fails. When a
slice tactic has added local entries and the book tactics take over,
search restarts from the admitted prefix. The session's fact names
also reserve names when the interface publishes proof-local entries.

The driver uses `h3-api-open` and `h3-api-prove-open` over whole books,
one session a book (`prover/OPEN.md`, "The test"). The test of the set is `sh prover/h3/test.sh`.
