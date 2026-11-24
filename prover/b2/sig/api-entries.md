# Proof-local entries

An entry is a four-element list `(kind name counts source)` as specified in
`prover/sig/library.md`. A group is `(names source)` with a list of declared
symbols and the group's source string. Lists of entries and groups are in
declaration order. Source strings contain ACL2 Core text, with a newline at
the end of each complete line.

| Call | Arguments and result | Failure |
|---|---|---|
| `(b2-api-entries-groups entries)` | Group declarations, joining a recursive definition to its following measure. | May return a failure while reading or matching a declaration. |
| `(b2-api-entries-dependencies entries entry)` | `entries` is a group list and `entry` is source text. Returns the list of transitive support groups in declaration order. | May return a failure when writing a name. |
| `(b2-api-entries-rename source names)` | Rename symbols at declaration, fact, and function positions in string `source` according to the name-to-name table `names`. | May return a failure when writing a candidate name or parsing or rewriting a line. |
| `(b2-api-entries-assemble prelude entries entry public-facts public-definitions)` | `prelude` is a group list, `entries` an entry list, and `entry` the statement's proof text. The last two arguments are tables keyed by symbol. Returns `(lemmas entry)` with support strings in declaration order and the statement's proof string. | Failure in grouping, finding dependencies, renaming, or resolving conflicting or repeated proof-local declarations. |
