# B2 sessions

A session is an ACL2 list with the empty-prefix context, prelude,
current-prefix context, most recent parsed statement, and measure table
cache. A prefix context contains its earlier lines, the admitted public
Library, an index of admitted lines, and the working Library with
prelude support. The empty-prefix context contains the admitted library
supplied to `b2-api-open`.

The line index groups normalized line strings by byte length and retains
the parsed statements. Prelude support replaces a public fact or
definition at its existing position when the names coincide. Other
support entries follow the public entries in declaration order.

## Earlier lines

When the earlier lines extend the current prefix, admission processes
only the suffix. The last parsed statement is available if its line is in
that suffix. When the earlier lines shrink or change order, admission
starts from the empty-prefix context and can reuse parses from the last
prefix. A failed admission leaves the last successful prefix in the
session.

A recursive definition requests a measure table keyed by the complete,
ordered aids list. The session holds up to four tables, in order of most
recent use. Temporary facts and auxiliary proof steps are local to the
proof attempt. The proof answer carries the supporting entries it uses.

`grep -nE 'b2-api-open|b2-open-extend-prefix|b2-open-measures' prover/b2/open.lisp`
shows the session operations. The command was run on 2026-11-23.

## The test

The driver uses `b2-api-open` and `b2-api-prove-open` over whole books,
one session a book (`prover/OPEN.md`, "The test"). The test of the set is `sh prover/b2/test.sh`.
