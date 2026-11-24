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
| `(b2-reuse-supporting entries source start)` | Entries in insertion order, initial source bytes, and starting index or `:none`. Returns `(support source)`. Support is in insertion order. Its source is appended while visiting entries from last to first. | Reading a header or writing a name. |
| `(b2-reuse-compiled-replay compiled lib)` | Compiled object and Library. Returns `(cons entry lib)` including appended definitions and lemmas. A failed match returns `(cons nil lib)`. | Parsing or installing a declaration. |
| `(b2-reuse-reuse-init)` | Returns an empty Reuse object with zero hits. | — |
| `(b2-reuse-reuse-lookup reuse raw lib)` | Reuse object, input byte string, and Library. Returns `(entry reuse lib)` with the first matching entry, or `nil` in the entry field if none match. | Replaying a compiled proof. |
| `(b2-reuse-reuse-remember reuse raw lib entry mark)` | Reuse object, input byte string, Library, entry, and starting entry index. Returns the Reuse object with the example appended. | Parsing a reference or looking up a required fact. |

`b2-reuse-compiled` takes the three record fields in order and returns a
Compiled object. `b2-reuse-compiled-entry`, `b2-reuse-compiled-support`
and `b2-reuse-compiled-facts` each take the record and return the field
named. `b2-reuse-reuse-compiled` and `b2-reuse-reuse-hits` take a Reuse
object and return the field named.

The required-fact alist built by `b2-reuse-reuse-remember` follows the
first occurrence of each required fact reference in the gathered proof
text. Replay compares the value of each required fact with the available
clause.

`*b2-reuse-fact*` is the pattern for a fact line in proof text. It gives
the literal prefix, minimum body length, and literal suffix. The pattern
matches a complete line between newline separators.
