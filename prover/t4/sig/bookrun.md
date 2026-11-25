# Book proof entries

An Entry is a record of the form `(:entry name source steps reason)`. A name is
a prover symbol. The source and reason are strings. Source contains proof text with its line endings. An empty reason denotes a proved
entry. `kind` is a statement word and `data` is its field list.

| Call | Result | Failure |
|---|---|---|
| `(t4-bookrun-make-entry name source steps reason)` | The Entry with those fields. | None. |
| `(t4-bookrun-skipped name reason)` | An Entry with the serialized skip and zero steps. | A failure from serializing the name. |
| `(t4-bookrun-obligation kind data)` | The name of the statement's first obligation, or `nil`. For a definition, the call search ends at the first recursive call. | A failure from inspecting statement fields or walking the calls up to that point. |
| `(t4-bookrun-sections source)` | The list of proof sections, each a list of its lines with their original endings, in source order. | A failure for a line with no word after the first byte. |
| `(t4-bookrun-enabled-functions hints)` | Names under ENABLE forms in depth-first order, with repeats. | None for parsed hints. |
| `(t4-bookrun-book-entry name kind raw generated evaluator simple)` | The Entry for the requested name. `raw` is the original statement line. `generated` is the primary `(steps source)` or failure. For a constraint with an `unproved` primary result, `evaluator` and `simple` are the respective witness results, each `(steps source)`, `nil`, or a failure. Supply `nil` for an unused witness result. | Failures outside the handled proof failures propagate. |
| `(t4-bookrun-witness-suffix raw)` | The uppercase first 12 hexadecimal digits of the statement's SipHash-2-4 digest. | None. |

`t4-slice-book-entry` calls the proof routines in order and supplies their
results to `t4-bookrun-book-entry`. The worklist, files and checker process
belong to the caller of the logic books.
