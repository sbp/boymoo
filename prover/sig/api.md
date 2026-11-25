# `api.lisp`

`(api-prove statement earlier library aids)` takes a statement string and
three groups of input lines. Each group may be a list of strings or a
single string with line breaks. Success returns `(lemmas entry)`, with
a list of auxiliary entry strings and the proof entry string. Trailing
newlines are part of the proof text. Exported auxiliary names use the
prefix `T1`. An unsuccessful proof attempt or input failure returns
`nil`.

The package is `BOYMOO-PROVER`. A proof context has the form
`(:context lib index seen declared helpers)`. The last three fields
hold distinct normalized lines, declared names and auxiliary names.
`api-context-make` constructs the context from its five fields.
`api-context-lib`, `api-context-index`, `api-context-seen`,
`api-context-declared` and `api-context-helpers` read the named field.

| Function | Arguments | Result |
|---|---|---|
| `api-raw-line` | `line`, a string | The line with CR and LF stripped from the right. |
| `api-as-lines` | `lines`, a list of strings or a multiline string | A list of lines. |
| `api-parse` | `raw`, a statement or proof line without its final newline | The list `(kind fields)` or a reader failure. |
| `api-hints` | `lines`, a list of input lines | The alist of measure entries keyed by the function symbol. May return a reader failure. |
| `api-statement-names` | `kind`, a statement kind string, and `data`, its parsed fields | The set of names introduced by the statement, as a list. |
| `api-choice-axiom-values` | `actual`, a call, and `bound`, the bound variables | The substitution alist for the choice term. |
| `api-choice-axiom` | `data`, the parsed fields of a choice statement | The fact term made available by the choice. May propagate a failure from a term operation. |
| `api-context-init` | No arguments | The context for an empty input prefix, or a failure from building the initial library and fact index. |
| `api-context-append` | `context`, a context, and `line`, an input string | The updated context, or a failure from parsing, indexing or using an auxiliary name. |
| `api-context-working-copy` | `context`, a context | `(lib index)` for a proof attempt in the prepared context. |
| `api-context-for` | `earlier` and `library`, each a list of input lines | The context for the library followed by the earlier input, or a failure from building or appending to it. |
| `api-replace-names` | `source`, the text of a proof entry, `aliases`, an alist from original to auxiliary symbols, and `statement-entry`, a Boolean | The transformed proof text, or a failure from reading or writing an entry. |
| `api-exported` | `certificate`, a certificate, and `declared`, the set of declared input symbols as a list | `(lemmas entry)`, `nil` on a name collision, or a failure from inspecting or rewriting the certificate. |
| `api-prove-in-context` | `statement`, `earlier`, `library` and `aids`, as for `api-prove` | `(lemmas entry)` or `nil` on proof failure. May propagate a failure from input or export processing. |

`*api-prefix*` is the string `"T1"`.

`(api-proof-obligation statement)` takes a statement string. It returns
`(raw kind data name)` when the statement needs a proof, `nil` when it
does not, or a failure from reading or inspecting the statement.

`(api-context-append-lines lines context)` appends a list of input
lines to a prepared context in order. It returns the extended context
or a failure from reading or indexing a line.

`(api-prove-context-statement raw context kind data name aids)` takes
the four fields of a proof obligation, a prepared context and the input
aids. It returns `(lemmas entry)`, `nil` on proof failure or a failure
from input or export processing.

`(api-context-with-seen context seen)` gives the context with its
seen-line set replaced.

`(api-context-parse-line raw remembered)` parses a normalized input
line if its kind is eligible for the context. It returns
`(kind fields)`, `nil` for an ignored line or a reader failure. If
`remembered` is a pair of the same raw line and its parse, that parse
is reused.

`(api-context-append-record context raw parsed)` appends a fresh
normalized line using the result of `api-context-parse-line`. It
returns the extended context or a failure from reading or indexing.

`(api-proof-obligation-parsed raw parsed)` uses a normalized
statement and its parse to produce the same obligation, refusal or
failure as `api-proof-obligation`. A `nil` parse gives `nil`.

`(api-prove-context-with-hints context kind data name hints)` proves
an obligation whose raw text has already been checked against the
context. The hints are a prepared measure alist or a reader failure.
It gives the same result forms as `api-prove-context-statement`.
