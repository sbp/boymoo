# Prover data and assembly

`prove-prover-run` makes rows for statement lines absent from the library and
the preceding statement lines. Each obligation gets an entry with its input
line number. Each selected obligation also gets a target.
The target carries its aid lines in input order and its tactic order with
rational seconds.

The prefix keeps `lines` in reverse order for constant-time additions.
`prove-prefix-lines` gives the earlier lines in input order.
`cache-subset-dependencies` takes the name and package digest maps from the
caller and scans the certificate and statement for named declarations.
The symbol scan skips quoted strings. The presence of a package operation's
name anywhere in the text adds every package declaration to the dependency set.

`prove-valid-blocks` checks the main entry opening, the helper openings,
ASCII text, terminal line feeds, and embedded skip lines. Assembly emits
the main block for each certified entry and emits each distinct helper
block at its first use. It writes a skip line for each uncertified entry
and returns the proof text with cumulative line-feed counts.

`prove-prover-checked` returns the zero-based position of the certificate
to drop. A proof-line rejection uses the first cumulative proof line
count at or beyond the location. A statement-line rejection uses the last
statement number at or before the location. In either case the decision
uses the latest certified entry in that prefix or, if the prefix has none,
the latest certified entry overall. An unclassified verdict with an
unconfirmed skip count uses the largest certificate and breaks ties by
input order. `prove-prover-checked-halve` uses certificate byte sizes in
descending order to bring the total to at most half its original size.
