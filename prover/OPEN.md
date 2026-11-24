# Sessions: the library prepared once

This file adds to `prover/CONVENTIONS.md`.

## Why

A run over a book calls a set of tactics hundreds of times with one library. Parsing the library, admitting its lines and building the set's indexes cost far more than most single attempts, so that work is done once and carried in a value, a **session**.

## The four functions of every set

The last book of each set is `open`: `prover/SET/open.lisp`, and `prover/open.lisp` for T1, whose functions have no prefix. With the set's prefix (`h4-`, `b2-`, ..., and none for T1):

```
(SET-api-prove statement earlier library aids)       the answer
(SET-api-open library)                               a session
(SET-api-prove-open session statement earlier aids)  (cons answer session2)
(SET-api-prove-all library cases)                    the list of the answers
```

`library`, `earlier` and `aids` are lists of lines, `statement` is a line, and `cases` is a list of `(statement earlier aids)`. An answer is the lemmas and definitions that the proof brings and the entry of the statement, or `nil` when the set has no proof, or a failure (`prover/FAILURES.md`).

1. **The answer is the same object.** `answer` is exactly the value of `(SET-api-prove statement earlier library aids)` for the library the session was opened with, character for character.
2. **A session only saves work.** `session2` is a session of the same library; it may hold more finished work than `session`. Any session of a library gives the same answers as any other. Only the time differs.
3. **`prove-all` passes one session along.** It opens the library once, calls `prove-open` on each case in order with the session the call before returned, and returns the answers in order.
4. **The library is read once.** Whatever the set computes from the library alone, and whatever it computes from nothing (its ground theory, its tables), is computed once for a session: in `open`, or at first need and then kept in the session that is returned. After that no call of `prove-open` parses, indexes or walks the lines of the library again.
5. **The earlier lines.** Where a call is cheaper because `earlier` begins with the `earlier` of the call before and has more lines at its end, the session keeps what was made of those lines. Each set's `notes/open.md` says what its session keeps.
6. A session is a plain ACL2 object. No `state`, no stobj, no array, no `hons`, no `memoize`.
7. A session does not grow at every call without bound. It keeps what belongs to the library and to the earlier lines; a table that only remembers single statements is kept only if a run over a book meets the same statement again.

## The test

The driver opens a session for each set with `SET-api-open` and gives it each statement with `SET-api-prove-open`. The test of a set (`prover/CONVENTIONS.md`, "Building and testing") therefore runs those two functions over whole books, one session a book, and has both checkers judge every proof that comes back. `SET-api-prove` and `SET-api-prove-all` are defined from the same two, by rules 1 and 3 above.
