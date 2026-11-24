# B2 proof interface

`(b2-api-prove statement earlier library aids)` takes one ACL2 Core statement
string and three lists of ACL2 Core line strings. The lists give earlier
statements, library statements and proof aids, respectively, in input order.
Each line can have a final newline.

The result is `nil` if no proof is returned. A proof result is
`(lemmas entry)`. The lemmas are a list of newline-terminated strings in
dependency order. A string for a local recursive definition includes its
measure entry. The entry is the newline-terminated proof of the requested
statement. Proof-local declaration names start with `PROVER-B2-`.
`b2-api-prove` returns `nil` when proof construction fails.

`*b2-api-prefix*` is the string `"B2"`. Library, Proof and Step use the
constructors and accessors in `prover/sig/library.md` and `prover/sig/proof.md`.
Facts, definitions and measures are association lists in first-insertion order. The seen set is a list of distinct strings, most recently admitted line
first. In this set, the line string excludes its final newline, if present.

| Call | Result |
|---|---|
| `(b2-api-parse raw)` | `(kind data)` for an ASCII line string without its final newline, or a failure from parsing. |
| `(b2-run-admit lib kind data)` | Updated Library after admitting parsed statement fields. May return a failure on malformed fields. |
| `(b2-api-fill lib lines seen)` | `(lib seen)` with the updated Library and seen set after admitting each previously unseen input line, or a failure. |
| `(b2-api-ground)` | The Tactics library with the ground facts and no entries. |
| `(b2-api-library lines)` | `(lib seen)` for the given list of library line strings, or a failure. |
| `(b2-api-prelude)` | `(lib groups)` containing the built base Library and its grouped support entries, or a failure. Each group is `(names source)` in declaration order. |
| `(b2-api-new-context source)` | A Tactics library with the facts, definitions and primitives of `source` and an empty entry list. |
| `(b2-api-measures aids)` | Association list from function symbols to measure terms for the `O<` relation, or a failure from parsing a measure line. |
| `(b2-api-claim lib name formula)` | `(lib compiled)` with the Library for the successful theorem attempt and the compiled theorem entry, or a failure. It tries facts in first-insertion order, then the shape, named and new theorem recipes in that order. |
| `(b2-api-prove-internal statement earlier library aids)` | The result of `b2-api-prove` with failures preserved. |

The one-shot and session interfaces share these proof steps.

| Call | Result |
|---|---|
| `(b2-api-definition-calls data)` | Calls for a parsed definition's ruler extenders and definitions, in source order, or a failure. |
| `(b2-api-compile-measured lib definitions calls measures)` | `(lib compiled)` for the recursive definitions with the given call list and measure table, or a failure. |
| `(b2-api-assemble-compiled public groups result)` | A proof answer from a public Library, the prelude groups, and the compilation result. Passes through a `nil` result or a failure. |
