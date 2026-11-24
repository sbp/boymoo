# T3 proof interface

`(t3-api-prove statement earlier library aids)` takes a statement line and
three sequences of lines in source order. A sequence can be a list of lines
or an ACL2 string containing line breaks.
`earlier` is the statement prefix at the obligation, `library` is the given
library, and `aids` holds aid records. The result is `nil` when the statement
has no proof, or `(lemmas entry)` where `lemmas` is the list of auxiliary
entry strings in dependency order and `entry` is the statement's proof
string. The terminating line feeds are part of these strings.

`*t3-api-prefix*` is `"T3"`. An auxiliary name keeps its symbol package and
uses `PROVER-T3-` followed by the sixteen uppercase hexadecimal digits of
the entry text's SipHash-2-4 value. The text includes the assigned names
of its dependencies. The entry's own name is assigned after hashing.

A parsed line is `(kind fields)`, with a string kind and a list of frozen
datums. The datum and entry representations are in `prover/sig/proof.md` and
`prover/sig/library.md`. `lib` is a book proof context. A scope has the form
`(:t3-api-scope lib seen search earlier)`. `seen` is the set of distinct
normalized input lines in first-admission order. `search` is the theorem
index, and `earlier` is the earlier sequence admitted so far. A measure map
is an association list of `(function-name . measure)` pairs in the order of
first assignment. A later assignment replaces the value in place.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t3-api-parse raw)` | Source line string. Returns its parsed line after stripping trailing line feeds. | A failure from parsing. |
| `(t3-api-text-lines lines)` | Sequence of lines or one string of lines. Returns a list of lines with their terminators preserved. | None on these forms. |
| `(t3-api-normalize-line line)` | One source line. Returns the line with a final line feed, adding it if necessary. | A failure if the argument is outside the line form. |
| `(t3-api-ground)` | The book proof context initialized with the ground declarations, the Library build, and the T3 arithmetic and size lemmas, in that order. | A failure from initialization or proof construction. |
| `(t3-api-helpers lib names base)` | Book proof context, list of trigger names, and Boolean for the base recipes. Returns the context after the applicable recipes, in source order. Use `:none` for the trigger without a function name. | A failure from a recipe or from discarding entries. |
| `(t3-api-library lines)` | Given library line list. Returns `(lib seen)` after admitting the distinct lines, then adding the base and triggered helper lemmas. | A failure from initialization, parsing, admission, or helper construction. |
| `(t3-api-scope-init library)` | Given library line list. Returns a scope with a theorem index and an empty earlier prefix. | A failure from library construction or indexing. |
| `(t3-api-scope-extend scope earlier)` | Scope and complete earlier line list. Returns the scope after admitting unseen lines following the length of its stored earlier prefix. New facts are indexed in admission order. | A failure from parsing, admission, helper construction, or indexing. |
| `(t3-api-context library earlier)` | Given library and earlier line lists. Returns the scope containing both in order. | A failure from library construction or scope extension. |
| `(t3-api-measures aids)` | Aid line list. Returns the measure map from lines beginning `(measure ` with the ordinal relation `ACL2::O<`. | A failure from parsing or accessing fields. |
| `(t3-api-own-names entries)` | The generated entry list, with auxiliary entries followed by the statement entry. Returns `(lemmas entry)` with auxiliary names and references rewritten in dependency order. | A failure from accessing fields or writing names. |
| `(t3-api-prove-core statement earlier library aids)` | Statement line and three line lists. Returns the proof and dependencies in the form of `t3-api-prove`, or `nil` for a statement without a proof. | A failure from parsing, indexing, proof construction, or writing. |
| `(t3-api-prove-input statement earlier library aids)` | As for `t3-api-prove-core`, with each line sequence normalized by `t3-api-text-lines`. | A failure from the input sequences or `t3-api-prove-core`. |
| `(t3-api-prove statement earlier library aids)` | Statement and input sequences, as described above. | None. |

For a single string, line boundaries are ASCII codes 10 through 13 and
28 through 30. A carriage return followed by a line feed ends one line.
Line lists retain the supplied boundaries.

`(t3-api-make-scope lib seen search earlier)` constructs a scope. The
accessors `t3-api-scope-lib`, `t3-api-scope-seen`, `t3-api-scope-search`, and
`t3-api-scope-earlier` each take one scope and return the named field.

Supply table triggers to `t3-api-helpers` as their ordered keys. When
discarding a helper attempt, a duplicate lemma entry removes the fact at
its name and leaves the earlier entry list in place.

The Library built by `t3-api-ground` carries the `:t3-book` Proof dispatch tag
keyword from `prover/t3/sig/logic.md`.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t3-api-proof-request statement)` | A statement line. Returns `(raw kind name data)` for an eligible obligation, or `nil`. The line is normalized to have a final line feed. | A failure from parsing or inspecting the statement. |
| `(t3-api-admit-prefix-line lib search kind fields)` | Book proof context, its theorem index and the kind and fields of an unseen earlier line. Returns the theorem index with the resulting context, including applicable helpers and newly indexed facts. | A failure from admission, helper construction or indexing. |
| `(t3-api-prove-prepared lib search kind name data measures)` | Book proof context, its theorem index, an eligible obligation's kind, name and data, and its measure map. Returns the proof and dependencies in the form of `t3-api-prove`. | A failure from proof construction or writing. |
| `(t3-api-proof-request-from-parsed raw parsed)` | Normalized statement line and its parsed `(kind fields)`. Returns the same obligation record as `t3-api-proof-request`. | A failure from inspecting the statement. |
| `(t3-api-library-helpers lib)` | Book proof context containing the given library. Returns the context with the library helper recipes applied in order. | A failure from helper construction. |
