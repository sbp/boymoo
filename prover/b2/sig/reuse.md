# Proof replay

A Compiled record has the form `(:compiled entry support facts)`.
Entries have the form in `prover/sig/library.md`. `support` is a list of
entries in declaration order. `facts` is an alist of required names and
clauses. A Reuse object has the form `(:b2-reuse compiled hits)`.
`compiled` is an alist keyed by the input statement byte string in order
of first insertion. Each value is a list of Compiled objects in order
remembered. `hits` counts successful replays.

| Function | Arguments and result | Failure |
|---|---|---|
| `(b2-reuse-parse raw)` | One proof line as a byte string. Returns `(word data)` with frozen data. | Reading or freezing the line. |
| `(b2-reuse-head entry)` | Entry. Returns its source through the first newline, excluding the newline. | — |
| `(b2-reuse-declares entry)` | Entry. Returns the declared names in source order. | Parsing the definition header. |

`*b2-reuse-fact*` is the pattern for a fact line in proof text. It gives
the literal prefix, minimum body length, and literal suffix. The pattern
matches a complete line between newline separators.
