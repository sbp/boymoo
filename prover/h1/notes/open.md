# H1 sessions

`h1-api-open` prepares the ground theory and derived library, admits
the supplied library declarations, and runs the base and declaration
installers. The library world keeps the theorem and schema indexes,
rules, available symbols, and evaluator equations. It records declared
names and indexes distinct lines in a balanced search tree after removing
their terminators.

The session keeps the library world, the most recent nonempty admitted
prefix, and up to four parsed measure tables indexed by their aid-line
lists. The most recently used measures come first.

When the supplied prefix extends the remembered one, the session admits
the new suffix in order. A different nonempty prefix is admitted from the
library world and takes the remembered prefix's place. An empty prefix
uses the library world while preserving the remembered prefix. Each new
declaration's installers run in order.

When admitting a prefix succeeds, the session keeps it even if proof
search is unsuccessful. Each proof attempt uses its own immutable
prover value. `h1-api-prove-all` threads one session through the cases in
order.

The driver uses `h1-api-open` and `h1-api-prove-open` over whole books,
one session a book (`prover/OPEN.md`, "The test"). The test of the set is `sh prover/h1/test.sh`.
