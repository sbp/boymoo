# H3 proof interface

`(h3-api-prove statement earlier library aids)` takes one statement line
and three lists of lines in input order. Each line is an ASCII string.
`earlier` contains the declarations preceding the statement. `library`
contains the given declarations and `aids` holds the aid records for
the file. The result is `(lemmas entry)` or `nil` if H3 gives no proof.
`lemmas` lists the cited local entries in dependency order and `entry`
is the proof of the statement. Both retain their terminating newlines.

`*h3-api-prefix*` is `"H3"`. Local entries retain their symbol packages and
receive names of the form `PROVER-H3-LABEL-DIGEST`. `LABEL` is the original
label with a leading `SELF-` removed. `DIGEST` is the sixteen-digit
uppercase SipHash-2-4 digest of the entry text after its local citations
and calls are renamed.

The Library, Step and datum representations are in `prover/sig/library.md`
and `prover/sig/proof.md`. A parsed line is `(kind fields)`, where `kind` is a
string and `fields` is the list of parsed datums. An `Entries` object has the
form `(:h3-api-entries entries tokens reserved names output active)`. `entries`
is the insertion-ordered association list from local symbols to entry text.
`tokens` is the list of those keys as written proof text, in the same order.
`reserved` is the set of other fact names in fact insertion order. `names`
is the insertion-ordered association list from local symbols to their assigned
names. `output` is the list of renamed entries in emission order. `active` is
the set of entries being visited, with the most recently added first.
Functions that update `Entries` return `(cons value object)`.
The first argument `n` is a natural-number recursion counter. Pass `1000000`
at the initial call. Zero fuel returns a `Fuel` failure.

| Call | Arguments and result | Failure |
|---|---|---|
| `(h3-api-read raw)` | The parsed line from `raw` after stripping trailing CR and LF. | A reader failure. |
| `(h3-api-admit lib kind fields)` | The Library after adding the declarations of the given parsed statement. | A failure from accessing or unpacking fields. |
| `(h3-api-admit-lines lib lines)` | The Library after admitting the definitions, constraints, theorems and axioms in `lines`, in order. | A failure from parsing or admission. |
| `(h3-api-library lines)` | The ground Library extended by the given list of library lines. | A failure from admission. |
| `(h3-api-world library earlier)` | The ground Library extended by the library lines and then the earlier lines. Its local entry list is empty. | A failure from admission. |
| `(h3-api-measures aids)` | The parsed measure records from the lines of `aids`, in their input order. | A reader failure. |
| `(h3-api-entries-init lib)` | An `Entries` object for the Library's local entries and reserved fact names. | A failure from writing a token. |
| `(h3-api-entries-name n object symbol)` | The renamed `symbol` and the resulting object. An external symbol keeps its name. A newly cited local entry is emitted after its dependencies. | A failure from the entry text, a cycle, a reserved name collision or fuel exhaustion. |
| `(h3-api-entries-term n object term)` | The term with local function names rewritten, and the resulting object. | A failure from traversal, renaming or fuel exhaustion. |
| `(h3-api-entries-substitution n object bindings)` | The rewritten bindings and the resulting object. `bindings` is the list of `(variable term)` pairs, or the prover datum for `NIL`. | A failure from unpacking bindings, rewriting or fuel exhaustion. |
| `(h3-api-entries-fields n object kind fields own)` | The rewritten parsed fields and the resulting object. `own` is the local entry symbol whose header is being visited, or `nil` for an ordinary line. | A failure from accessing fields, rewriting or fuel exhaustion. |
| `(h3-api-entries-rewrite n object text own)` | The rewritten proof text and the resulting object. `own` has the same meaning as in `h3-api-entries-fields`. | A failure from parsing, rewriting or fuel exhaustion. |
| `(h3-api-prove-core statement earlier library aids)` | The parsed obligation's proof and dependencies in the form returned by `h3-api-prove`, or `nil` for an unsupported statement kind. | A failure from proving or emitting the entry. |

`(h3-api-prove-admitted parsed lib aids rebuild)` proves a parsed
obligation in a Library that already includes the earlier lines. The
result has the same form as for `h3-api-prove-core`, including failures.
`rebuild` is `nil` to reuse the admitted Library when book tactic
search follows a failed slice attempt. The pair `(library earlier)`
supplies the lines for rebuilding that Library.

`(h3-api-read-declaration raw)` reads a library or earlier line. It
returns the parsed declaration, `nil` for a line admission ignores, or
a failure. `(h3-api-admitted-names kind fields)` returns the names assigned
by a successful `h3-api-admit`, in their order of assignment.

`(h3-api-prove-with-prepared-facts parsed lib measures prepared)` proves
the parsed obligation in the admitted Library. `measures` is the result
of `h3-api-measures` for a definition and `nil` for other obligations.
`prepared` is the fact index preparation for `lib`. The result has the
same form as for `h3-api-prove-core`, including failures.
