# Book proof selection

`p` is the H4 Tactics library. Terms, proof names, and Steps use the forms
in `prover/sig/proof.md`. A Statement has the form
`(:h4-statement kind fields name calls)`. Its `kind` is a string and its
`fields` are the parsed statement fields in source order. Its `name` is a
prover symbol, or `nil` for a statement without a proof obligation. Its
`calls` are the Call records of `prover/sig/termination.md` in source order.
A Certificate has the form `(:h4-certificate proof steps support reason)`.
`proof` is the entry's source string, `steps` is its step count, `support`
is the list of auxiliary entry sources in library order, and `reason` is
the reason string, empty for a proved entry.

| Call | Result |
|---|---|
| `(h4-book-run-make-statement kind fields name calls)` | Statement with the supplied fields. |
| `(h4-book-run-statement-kind statement)`, `(h4-book-run-statement-fields statement)`, `(h4-book-run-statement-name statement)`, `(h4-book-run-statement-calls statement)` | The named field of the Statement. |
| `(h4-book-run-make-certificate proof steps support reason)` | Certificate with the supplied fields. |
| `(h4-book-run-certificate-proof certificate)`, `(h4-book-run-certificate-steps certificate)`, `(h4-book-run-certificate-support certificate)`, `(h4-book-run-certificate-reason certificate)` | The named field of the Certificate. |
| `(h4-book-run-parse-statement raw)` | Statement read from the byte string `raw`, including its final line terminator. |
| `(h4-book-run-witness-definitions p arities)` | `(cons models p)` with the updated Tactics library and an ordered alist from `(arity label)` to a witness function name. Arities are in ascending order, with `"NIL"`, `"T"` and, for positive arities, `"first argument"` inserted in that order. |
| `(h4-book-run-replace-functions term witnesses)` | `term` with its function positions renamed according to the alist from function names to witness names. |
| `(h4-book-run-witness-proof p fields models)` | `(witnesses proofs)` with the first successful witness assignment and its Steps. `fields` are the two fields of a constrain statement. |
| `(h4-book-run-find-proof p statement measures hints models printing ordering conversions)` | `(cons (list kind arguments proofs) p)` with the proof entry kind, header argument list, Step list, and resulting Tactics library. |
| `(h4-book-run-prove-statement p statement measures hints models printing ordering conversions)` | `(cons certificate p)` with the certificate and resulting Tactics library. |
| `(h4-book-run-entry-sources p last final-source)` | List of `(steps source)` pairs for auxiliary entries used by the final proof Step `last` and its entry text `final-source`, in library insertion order. |

Proof calls can return a failure in place of their whole result. An
`Unproved` witness attempt advances to the next assignment. An exhausted
witness or proof search returns `Unproved`. `models` is the witness alist
described above. `measures` and `hints` are insertion-ordered alists from
names to lists of `(measure relation)` pairs and hint uses, respectively.
`printing` and `ordering` are the support alists of their respective
books. `conversions` is the two-element list of the `ExpansionProofs`
and `InversionProofs` objects, using their owners' representations.

File contents cross the logic interface as strings. A manifest is the
list of `(book count)` pairs in manifest order. The source map is an
alist from book name strings to complete source strings.

| Call | Result |
|---|---|
| `(h4-book-run-catalogue library manifest sources)` | `(statements books common)`. `library` is the list of library line strings, including line endings. `statements` are in order of first occurrence and `books` is the ordered alist of book names to statement indices in book order. `common` maps obligation indices to their sets of shared earlier indices. Its keys follow first occurrence of the obligations and its set members follow the string order of their decimal spellings. A parse error, missing source or manifest count mismatch produces a failure. |
| `(h4-book-run-aids-from-books manifest sources)` | `(measures hints)` in the forms above. The first occurrence of a name fixes its position and the first occurrence of a value fixes its position within the name's list. A missing aid source is skipped. Can return a parse failure. |
| `(h4-book-run-update-results manifest book rows existing)` | Result text from `existing` results text with the given book's entries replaced by `rows`, a list of row strings. Library rows retain source order and book groups follow manifest order. |

Signal handling, file I/O, checker invocation, and the command line are
outside the logic book.

`(h4-book-run-find-proof-with-context p statement measures hints models
printing ordering conversions book-functions)` returns `(list result p
conversions)`, or a failure. `result` is `(kind arguments proofs)` and both
objects are the values after the call. `book-functions` is the caller's
set of constrained and chosen function names and is used by membership.
This entry point retains both conversion objects for subsequent proofs.
`h4-book-run-find-proof` accepts an optional third element in `conversions`
for the same set and returns only the result paired with the Library.
`h4-book-run-prove-statement-with-context` takes the same arguments as the
contextual proof search and returns `(list certificate p conversions)` or
a failure. `h4-book-run-prove-statement` accepts the same optional third
element and returns the Certificate paired with the Library.

The batch computation uses two calls. The library argument is the complete
library source string. The selected book names follow selection order.
Statement and aid sources use the source maps described above.

| Call | Result |
|---|---|
| `(h4-book-run-generate-books-prepare manifest selected library statement-sources aid-sources)` | A request with the catalogue, origins, aids and Tactics library after statement admission and propositional lemmas. |
| `(h4-book-run-generate-books-library request)` | The Tactics library on which the caller builds the H4 library lemmas. |
| `(h4-book-run-generate-books request built)` | `(books distinct-proved distinct-skipped)`, where `built` is the library after that build and before the countdown lemmas. Each book result is `(book proof-source rows skipped)` in selection order with rows in obligation order. |

The preparation and assembly calls can return a failure. An `Unproved`
result produces a skip entry with the reason `unproved`. The caller supplies the library
build carried out by the H4 interface and supplies file and checker operations
outside the logic.

`(h4-book-run-generate-books-from-sources manifest selected library
statement-sources aid-sources)` prepares the same batch, carries out the
H4 library build, and returns the same book results and counts as
`h4-book-run-generate-books`. It can return a failure from any of these calls.

`(h4-book-run-find-proof-with-templates p statement measures hints models
printing ordering conversions book-functions tables)` takes the template
tables of `book-tactics.md` and returns the same result as
`h4-book-run-find-proof-with-context`.
