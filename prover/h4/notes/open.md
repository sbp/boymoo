# H4 sessions

A session holds an admitted library and its latest successfully admitted
prefix of earlier lines. A world contains facts, definitions, constrained
functions and choices. The session uses exact source lines as keys for
admission and parsing. A rule template records the rule views and lookup
keys of one fact clause.

| Stored value | Preparation and reuse |
|---|---|
| Ground and library worlds | `h4-api-open` prepares the ground templates and admits the distinct library lines. |
| Earlier lines | `h4-open-admit-lines` stores their parsed statements and rule templates. The session also has the most recent parsed target. |
| Aids | Up to 16 sets of measures and hints, keyed by their input lines. |
| Core support | Proof entries, facts, definitions and templates, built on first use. |
| Pointwise support | Up to four results, keyed by the `FN-EQUAL` definition and the `APPLY$-EQUIVALENCE-NECC` clause. |
| Warrant support | The most recent prelude, keyed by the ordered definitions it uses. The support contains entries, aliases, facts, definitions and filter names. |
| Auxiliary entry names | Up to 512 entries, keyed by kind, name, source, dependency aliases and name-matching mode. |

When `earlier` extends the latest prefix, the session admits only its
new suffix. A shorter or divergent prefix starts from the admitted
library and can reuse parsed lines. The first occurrence of an exact
source line controls admission. A different declaration of an existing
name updates its fact or definition at its existing position. A failed
admission leaves the latest successfully admitted prefix available.

Book search assembles literal and equation indexes from the current facts
in reverse declaration order. It uses a rule template only when the
template's name and clause match the current fact. Current definitions
determine which facts enter the search.

Evidence lookups, normalization replies, conversion proofs and proof
serialization belong to the current proof attempt. Printing and ordinal
support are built when a target in the current world needs them. A new
auxiliary entry is named from its source with SipHash-2-4.

The driver uses `h4-api-open` and `h4-api-prove-open` over whole books,
one session a book (`prover/OPEN.md`, "The test"). The test of the set is `sh prover/h4/test.sh`.
