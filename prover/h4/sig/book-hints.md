# Explicit hint instances

`p` is a Library as specified in `prover/sig/library.md`. Terms and Steps
have the forms in `prover/sig/proof.md`. A function-name set is a list of
distinct names used for membership tests.

| ACL2 call | Arguments and result | Failure |
|---|---|---|
| `(h4-book-hints-applications item)` | Flattened fact names and explicit instances found in a hint item, in traversal order. | A malformed tagged item can return a failure. |
| `(h4-book-hints-hint-uses lines)` | List of `(statement-name use)` pairs from the input strings, retaining line order, hint order, and repeated uses. Trailing newlines are allowed. | Reader or malformed datum failures. |
| `(h4-book-hints-source-term term functions)` | Logical translation of a source term using the given function-name set. | `UnusableHint` for an unsupported source term or constant. A malformed term can produce a separate failure. |
| `(h4-book-hints-hint-facts p uses book-functions)` | List of fact Steps in use order. `book-functions` is the set of constrained and chosen function names. Definitions and primitives are obtained from the Library's Proof. | Fact-instantiation failures. Invalid source bindings are skipped. |

The constants are `*h4-book-hints-use*`, `*h4-book-hints-instance*`, and
`*h4-book-hints-divide*`. File input is supplied as lines to
`h4-book-hints-hint-uses`.
