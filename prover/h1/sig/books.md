# Book proof worlds

A BookProver extends the H1 prover from `prover/h1/sig/tactics.md` with
book-specific fields. `available` is a set of prover names. `schemas` is an alist in
insertion order from `(head argument-head)` keys to lists of
`(name formula free)` triples, in registration order. `free` is the set
of variables in `formula`. The `evaluators` field is an alist from evaluator
names to ordered lists of `(fact-name operation)` pairs. `search-work` and
`case-limit` are integers. The default values are 3000 and 18, respectively.
The Library and rule fields use the accessors in `prover/h1/sig/tactics.md`.

An entry is `(kind name counts source)`, with a kind string, a prover name,
an ordered list of step counts, and the complete source string.
`*h1-books-base-tactics*` is the list of base installer symbols in execution
order. `*h1-books-definition-tactics*` maps definition names to installer
symbols. `*h1-books-constraint-tactics*` maps constrained evaluator names to
lists of installer symbols in execution order. Installer symbols are the
ACL2 function names in the prover package, used as values.

| ACL2 call | Result | Failure |
|---|---|---|
| `(h1-books-book-prover-init)` | BookProver initialized with the ground facts and the propositional rules. | A failure from construction. |
| `(h1-books-book-prover-add-definition proof name formals body)` | The updated Prover with the definition and its name available. | A failure from adding the definition. |
| `(h1-books-book-prover-available proof)` | The set of available names, as a list. | — |
| `(h1-books-book-prover-schemas proof)` | The indexed schemas. | — |
| `(h1-books-book-prover-evaluators proof)` | The evaluator equations. | — |
| `(h1-books-book-prover-search-work proof)` | The current search work limit. | — |
| `(h1-books-book-prover-case-limit proof)` | The current case limit. | — |
| `(h1-books-book-prover-with-search-work proof search-work)` | Prover with the supplied search work limit. | — |
| `(h1-books-book-prover-with-case-limit proof case-limit)` | Prover with the supplied case limit. | — |
| `(h1-books-book-prover-solve proof formula openings limit)` | Step for `formula`, using the smaller of integer `limit` and the case limit. Use `nil` and 160 for omitted openings and limit. | `Unproved` or a failure from proof construction. |
| `(h1-books-book-prover-constant proof term)` | Constant-computation Step, or `nil` when there is none. | A failure from proof construction. |
| `(h1-books-book-prover-by-induction proof formula measure substitutions openings ordinal limit assume-premise preserve split-on)` | Induction Step with the smaller of the given limit and the case limit. Pass the ordered `(bindings descent-step)` substitutions and the given induction options. Pass `:none` for an omitted limit. | `Unproved` or a failure from proof construction. |
| `(h1-books-fact-key term)` | `(head argument-head)` for schema indexing. The second field is `nil` unless an equality, negation, or implication gives an argument head. | A failure from indexing a malformed term. |
| `(h1-books-book-prover-index-fact proof name formula)` | Prover with the schema indexed under the formula's key, if it has a head. | A failure from indexing or collecting variables. |
| `(h1-books-book-prover-record-formula proof label step rewrite)` | `(cons fact-step proof)` after registering the formula with its string label. Pass `nil` for the default `rewrite`. | A failure from proof construction or indexing. |
| `(h1-books-book-prover-prior-fact proof term)` | The first applicable fact Step, or `nil`. Exact matches precede schema matches. | A failure from matching or proof construction. |
| `(h1-books-book-prover-fork proof)` | A copy of the BookProver. | — |
| `(h1-books-install-reverse proof)` | Prover with the reverse-append rule. | A failure from proof construction. |
| `(h1-books-declaration-tactics kind fields)` | Installer symbols for the parsed declaration, in execution order. | A failure from reading malformed fields. |
| `(h1-books-install proof install)` | Prover after running the given installer symbol. | A failure from the installer. |
| `(h1-books-admit proof kind fields register-theorem)` | Prover updated with the parsed declaration. Pass `:register-theorem` for the book runner's theorem registration. | A failure from reading fields, registering a fact, or constructing evaluator equations. |
| `(h1-books-parse-measures lines)` | Insertion-ordered alist from names to `(measure relation)` pairs, with each later measure line replacing the previous value for its name. The lines are strings with optional CR and LF terminators. | A failure from parsing or unpacking a measure line. |
| `(h1-books-entry-names entry)` | List of the names declared by `entry`, in source order. | A failure from reading a malformed entry. |
| `(h1-books-theorem-entry proof fields)` | `(cons entry proof)` with the theorem entry and the Prover after the selected tactic. `fields` is `(name formula)`. | A failure from a tactic or proof construction. |

## Certificates

A Certificate is `(:h1-certificate entries facts reason)`. `entries` is
the ordered list of proof entries. `facts` is the ordered list of external
dependency pairs `(name clause)`. `reason` is a string, empty when a proof
was found. `(h1-books-make-certificate entries facts reason)` constructs
one. `h1-books-certificate-entries`, `h1-books-certificate-facts`, and
`h1-books-certificate-reason` each take a Certificate and return the named
field.

| ACL2 call | Result | Failure |
|---|---|---|
| `(h1-books-certificate-can-reuse certificate proof)` | Boolean indicating that the Prover has each exact dependency clause. | — |
| `(h1-books-certificate proof entry used-entries)` | Certificate for the supplied entry and its external dependencies. Pass `:used-entries` for the book runner's dependency selection. | A failure from reading proof text or looking up a dependency. |
| `(h1-books-skip name)` | A skip Certificate for `name` with reason `"no proof"`. | A failure from writing the skip entry. |

The proof interface supplies statement and aid lines as arguments.
Worklist and aid file reads, output paths and writes, and reporting are
handled outside ACL2.

`(h1-books-book-prover-build proof)` prepares the derived Library and
returns the resulting Prover or a failure. `(h1-books-used-entries entries
conclusion)` returns the selected transitive dependencies and `conclusion`
in entry order, or a failure from inspecting a malformed entry. It keeps a
definition and its adjacent measure together during selection. When the
schema index stores a missing head, it uses `:none` as specified by
`tactics.md`. `h1-books-fact-key` exposes the missing heads as `nil`.

The callback arguments can also be dictionaries of replies. The keys for
`register-theorem` are `(proof name formula)`, with the resulting Prover
or a failure as the value. The keys for `used-entries` are `(entries entry)`,
with the selected entries or a failure as the value.

When admitting a constraint, the `evaluators` dictionary retains its
existing positions and appends new evaluator names in the order supplied
by `h1-book-witness-evaluator-equations`.

## Book worklist computation

| ACL2 call | Result | Failure |
|---|---|---|
| `(h1-books-worklist source count)` | List of `(book expected)` pairs from the supplied worklist text, in order. Pass `:none` for no count limit. | A failure from parsing a selected row. |
| `(h1-books-aids-for book aids)` | The measure dictionary for `book` from the alist `aids` of book names to aid lines. | A failure from parsing an aid line. |
| `(h1-books-obligation proof raw kind fields measures memo used-entries report)` | `(item proof memo report-row)`. `item` is `(name certificate)` for an obligation, or `nil`. The insertion-ordered `memo` maps raw statement lines to successful Certificates, in production order. `report-row` is `(name-text message)` when `report` is true and the attempted obligation produces a skip, or `nil`. | A failure from inspecting a declaration or an failure propagated from proof construction. |
| `(h1-books-generate-books library worklist statement-lines aid-lines count register-theorem used-entries report)` | `(cons books reports)`. A book result is `(book proof-source rows skipped)` with the proof text, the list of tab-delimited rows, and the skip count. `library` is a list of raw statement lines with terminators. `worklist` is the worklist text. `statement-lines` and `aid-lines` map each book name to its input lines in order. `count` and the callback arguments have the forms above. | A failure from building the initial Prover, parsing a line, or processing an obligation. |

Reports are returned in occurrence order. The file layer supplies input
lines and writes the proof text to its chosen destination.
