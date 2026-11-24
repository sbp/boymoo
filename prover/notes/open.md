# T1 library sessions

`api-open` prepares a base context from the ground theory and the
given library. The context holds definitions, facts, primitives,
auxiliary entries, declared names and the ordered fact and shortening
equation buckets. Normalized given lines and their parses are indexed
by text in a balanced tree. The facts retain library order.

`api-prove-open` retains the most recent successfully prepared
earlier prefix and its context. When the prefix grows, the context
extends with the suffix. When it changes or shrinks, the call
extends the base context. A failed extension leaves the last
successful prefix available.

The session also keeps the latest successful statement parse and up
to four parsed measure-aid groups in recency order. Proof attempts
use the prepared context and their own search budget.
`api-prove-all` passes the resulting session along in case order.

The driver opens one session a book with `api-open` and gives it each
statement with `api-prove-open` (`prover/OPEN.md`, "The test"), so
`sh prover/test.sh` runs these two functions over whole books, and both
checkers judge every proof that comes back. Its table is `prover/expected.tsv`.
