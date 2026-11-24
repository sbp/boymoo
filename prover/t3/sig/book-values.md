# Primitive values and package declarations

A book proof context is `(:t3-book-values-book-proofs library packages visible)`. `library` is a Library from `prover/sig/library.md`. `packages` is an insertion-ordered alist from package name strings to import alists, which associate symbol name strings to symbol data in declaration order. Updating an existing import retains its position. `visible` is the list of distinct visible package names in first declaration order. A hidden declaration adds an import alist and leaves the visibility list as it was.

Use `(t3-book-values-make-book-proofs library packages visible)` to construct an object. The accessors `t3-book-values-book-proofs-library`, `t3-book-values-book-proofs-packages` and `t3-book-values-book-proofs-visible` each take one object and return the named field. `(t3-book-values-book-proofs-with-library book-proofs library)` replaces the Library and preserves the package fields. The constructor, accessors and replacement return their stated values.

`term` and Steps have the forms in `prover/sig/proof.md`. `datum` and `kind` in `coerce` are unquoted data. `evidence` is an ordered list of Steps. Pass `nil` for omitted evidence.

| ACL2 call | Result | Failure |
|---|---|---|
| `(t3-book-values-tagged value tag)` | Boolean indicating whether the nonempty tuple datum begins with string tag `tag`. | None. |
| `(t3-book-values-book-proofs-init ground)` | book proof context with the initialized Library and package state from the ordered list `ground` of parsed `(kind data)` statements. | A failure from reading a package declaration. |
| `(t3-book-values-book-proofs-declaration book-proofs kind data)` | book proof context with the package declaration of string `kind` and statement field list `data` processed. | A failure from reading a package declaration. |
| `(t3-book-values-book-proofs-natural book-proofs term)` | Step proving `term` natural. | A failure from proof construction. |
| `(t3-book-values-book-proofs-type-of book-proofs term evidence)` | Step proving `term` integer. | A failure from proof construction. |
| `(t3-book-values-book-proofs-constant book-proofs term)` | Constant computation Step or `nil` when no computation applies. | A failure from reading terms or proof construction. |
| `(t3-book-values-book-proofs-package-value book-proofs function datum)` | The imports or witness datum for the indicated package primitive and argument, or `nil` when unavailable. | A failure from reading a malformed datum or package state. |
| `(t3-book-values-book-proofs-coerce datum kind)` | Character list datum for the `COMMON-LISP::LIST` kind, or a string datum for another kind. | A failure from reading a malformed datum or converting byte codes. |

The symbol constants are `*t3-book-values-symbolp*`, `*t3-book-values-symbol-name*`, `*t3-book-values-char-code*`, `*t3-book-values-code-char*`, `*t3-book-values-coerce*`, `*t3-book-values-numberp*`, `*t3-book-values-package-name*`, `*t3-book-values-imports*`, `*t3-book-values-witness*`, `*t3-book-values-intern*` and `*t3-book-values-bad-atom*`.

`(t3-book-values-book-proofs-simplify book-proofs term evidence definitions)` and `(t3-book-values-book-proofs-normalize book-proofs term evidence definitions)` return a simplification Step or `nil`, applying the primitive computations of the book proof context. Normalization also unfolds the wrapper symbols from `prover/t3/sig/logic.md`. `(t3-book-values-book-proofs-prove book-proofs term evidence definitions)` returns a Step proving the given term. Each can return a failure, including `Fuel`.

The initialized Library has the `:t3-book` Proof dispatch tag specified in `prover/t3/sig/logic.md`. Use that Library class when constructing book proof context from an existing Library.

The book proof context primitive computations use the operations specified in `prover/t3/sig/book-spines.md`. Load `book-spines.lisp` before this book.
