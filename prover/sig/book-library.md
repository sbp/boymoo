# Book proof library

`BookLibrary` adds constant and Boolean rules to the slice theory and uses the Library
representation and constructor in `prover/sig/library.md`. `lib` is that
Library object. Terms and Steps have the forms in `prover/sig/proof.md`.
Each function can return a failure in place of its listed result.

| Function | Arguments in order | Result |
|---|---|---|
| `book-library-cons-value` | `head`, `tail` (quoted data) | Datum formed by adjoining `head` to `tail` |
| `book-library-book-library-build` | `lib` | Library with the book definitions and lemmas |
| `book-library-book-library-boolean-constant` | `lib`, `value` (quoted Boolean term) | Step proving Boolean type |
| `book-library-book-library-boolean` | `lib`, `term` | Step proving Boolean type, or `nil` |
| `book-library-book-library-false-value` | `lib`, `term`, `premise` (Step for the rejection of `term`) | Step proving equality to quoted `NIL` |
| `book-library-book-library-constant` | `lib`, `term` | Constant computation Step or `nil` |

`*book-library-booleanp*` is the `BOOLEANP` term symbol.
`*book-library-boolean-axioms*` maps recognizer symbols to fact names.

`book-library-book-library-init` takes an initialized Proof and returns
a Library whose proof uses the `:book` rules. The book build selects
these rules before constructing the slice entries.
