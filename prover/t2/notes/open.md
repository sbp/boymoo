# T2 library sessions

## Given statements

A session stores the Generator with the given statements admitted. The
same preparation indexes each parsed library event by its source text.
The session retains the enriched Generator and the flag indicating
whether every lemma family succeeded. Enrichment is computed at first
use of the book context.

Rule preparation stores the ordered index and the rules contributed by
each given clause. The search uses the effective clauses and definitions
after preceding statements are admitted and preliminary tactics run.
New facts extend the index in fact order. Replacing a clause or defining
its name changes which rules are available from that fact.

## Preceding statements

A session keeps the source lines and parsed events for the current
prefix. It stores admission snapshots for both the plain and enriched
contexts. When the prefix extends, each snapshot resumes admission at
its saved event count. The last target's parsed event can be reused
when that target appears in a later prefix. A different or shortened
prefix starts its own admission snapshots from the prepared library.

When a retry needs enrichment after admitting a nonempty prefix, the
lemma families run with the prefix in scope. Definitions and facts in
that prefix can provide premises for those families.

## Aids and helper text

The session keeps eight recent sets of aids with their parsed data
and merged measures. It also keeps up to 512 entries in each of two
helper caches. One cache holds qualified tokens per helper. The other
holds resolved bindings and rewritten proof text keyed by the source,
declared names, and earlier bindings. Each attempt checks private names
against its current facts. The main proof entry is written for the
current obligation.

The test of the set is `sh prover/t2/test.sh`.
