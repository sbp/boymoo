# B1 library sessions

## Library preparation

`b1-api-open` builds the ground Library and admits the supplied library
lines to prepare a proof context. The session holds the resulting
Library, formula map, occupied names, and rule index. A balanced search
tree maps each distinct library line to its parsed fields. It supports
statement recognition and duplicate checks during admission of earlier
lines. The package import map and ground declarations are book constants.

## Earlier lines and aids

A session keeps up to sixteen earlier-line checkpoints. Each checkpoint
ends at a multiple of 64 lines and is keyed by its exact prefix. The
prepared library supplies the empty prefix. A call admits the rest of
its earlier lines as a second group. Within each group, the fact index
uses the last clause for a repeated name at its first insertion position.

The session reuses the parses of matching lines at the same positions
in the preceding history. It also retains the last parsed statement
for use when that line enters the history. Definition obligations use
up to twelve cached measure maps keyed by their complete lists of aids.

Each proof attempt starts from the prepared context and has its own
search state and auxiliary entries. The certificate writer selects and
names the required auxiliary entries for that obligation.
`b1-api-prove-all` passes the latest session between cases.

## The test

The driver uses `b1-api-open` and `b1-api-prove-open` over whole books,
one session a book (`prover/OPEN.md`, "The test"). The test of the set is `sh prover/b1/test.sh`.
