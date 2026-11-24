# Statement worlds and proof export

A World is `(:h1-api-engine-world earlier proof seen names)`. `earlier` is
the supplied list of preceding lines. `proof` is a BookProver as described
in `prover/h1/sig/books.md`. `seen` contains the distinct library and preceding
lines with their final carriage returns and newlines removed. `names`
contains the distinct names declared by those lines. The sets use lists
with members in order of first occurrence. The constructor
`h1-api-engine-make-world` takes the four fields in order. The accessors are
`h1-api-engine-world-earlier`, `h1-api-engine-world-proof`,
`h1-api-engine-world-seen`, and `h1-api-engine-world-names`.

Book entries are the `(kind name counts source)` records in
`prover/sig/library.md`. Statement fields are reader data in the form
described in `prover/sig/reader.md` and `prover/sig/proof.md`. A line is an
ASCII string. `nil` denotes an empty list of lines.

| ACL2 call | Result | Failure |
|---|---|---|
| `(h1-api-engine-prove statement earlier library aids)` | Either `nil` or `(auxiliaries entry)`. The auxiliaries are a list of proof entry texts in dependency order and `entry` is the statement's proof entry text. Each text includes its trailing newline. `statement` is one line. Each other input is a list of source lines, a source string containing line breaks, or `nil`. | A failure from parsing, constructing or exporting the proof. |
| `(h1-api-engine-as-lines source)` | List of lines from the string `source`, keeping each terminator, or the supplied list of lines. `nil` gives an empty list. A string source uses ASCII text line boundaries. | — on these inputs. |
| `(h1-api-engine-parse raw)` | Two-element list `(kind fields)` from source line `raw`, after stripping final carriage returns and newlines. | A failure from the reader. |
| `(h1-api-engine-statement-names kind fields)` | Names the statement declares, in declaration order. | A failure from reading malformed fields. |
| `(h1-api-engine-attempt-install proof install)` | BookProver extended by the installer identified by `install`, a tactic identifier from `books.lisp`. On installer failure, returns `proof`. | — on these inputs. |
| `(h1-api-engine-given-world library)` | World with no preceding lines, after admitting the ordered list of library lines and attempting its tactic installers. | A failure from constructing the world or admitting lines. |
| `(h1-api-engine-statement-world earlier library)` | World for the ordered lists of preceding lines and library lines. | A failure from constructing the world or admitting lines. |
| `(h1-api-engine-measures aids)` | Dictionary mapping function names to `(measure relation)` from the ordered list of aid lines. Keys occur in order of first insertion. | A failure from parsing the lines or their measure fields. |
| `(h1-api-engine-write-atom datum)` | Atomic reader datum serialized as a byte string. | A failure from the writer for an invalid datum. |
| `(h1-api-engine-write-frozen datum)` | Frozen datum serialized as a byte string. | A failure from the writer for an invalid datum. |
| `(h1-api-engine-quotation-end source start)` | Byte offset immediately after the closing parenthesis of a quotation in `source`. `start` is the offset after its opening token. | A failure for an unclosed quotation. |
| `(h1-api-engine-scoped-symbols source names)` | `source` with selected unescaped generated symbols replaced outside quotations. `names` is an insertion-ordered alist from symbol text to replacement text. | A failure for an unclosed quotation when scanning for replacements. |
| `(h1-api-engine-auxiliary-groups entries)` | Auxiliary entries grouped in order, with each adjacent matching definition and measure kept together. | A failure for an entry that is neither a definition nor a lemma outside a pair. |
| `(h1-api-engine-export proof entry public)` | Two-element list `(auxiliaries entry-text)` for the BookProver's auxiliary dependencies and the conclusion `entry`, or `nil` for a name collision or an auxiliary without a generated name. `public` is a list of distinct public names. | A failure from reading or exporting the entries. |

`h1-api-engine-as-lines` returns a failure for input outside the listed
forms. Removing line terminators requires a string.

| ACL2 call | Result | Failure |
|---|---|---|
| `(h1-api-engine-proof-target statement)` | `(raw kind fields calls)` for a proof obligation, or `nil` for a line with no obligation. `raw` is the line without its terminators. | A failure from reading the line or determining its obligation. |
| `(h1-api-engine-define-entry proof fields calls measures)` | `(cons entry proof)` for the termination proof. `fields` are the parsed definition fields, `calls` are the recursive calls, and `measures` is the parsed aid dictionary. | A failure from constructing the proof. |
| `(h1-api-engine-finish-entry built kind fields names)` | The public answer for `(cons entry proof)` in `built`. `kind` and `fields` describe the target declaration. `names` supplies the public names from the world. | A failure from `built`, name extraction, or export. |
| `(h1-api-engine-given-proof)` | BookProver with the ground theory, derived library, rules, and selector tests ready to admit declarations. | A failure from initialization. |
| `(h1-api-engine-admit-line raw proof)` | `(proof2 parsed names)` after admitting a line whose terminators have been stripped and whose text is new to the world. `parsed` is `(kind fields)` and `names` is the list of names the declaration supplies. | A failure from parsing, admission, or name extraction. |
| `(h1-api-engine-install-given proof installers)` | BookProver with the base tactics and then the library's declaration tactics attempted. `installers` holds the declaration tactics in reverse order. | — on these inputs. |
