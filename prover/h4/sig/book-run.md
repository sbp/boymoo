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
| `(h4-book-run-entry-sources p last final-source)` | List of `(steps source)` pairs for auxiliary entries used by the final proof Step `last` and its entry text `final-source`, in library insertion order. |

Proof calls can return a failure in place of their whole result. An
`unproved` witness attempt advances to the next assignment. An exhausted
witness or proof search returns `unproved`. `models` is the witness alist
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

Signal handling, file I/O, checker invocation, and the command line are
outside the logic book.

The batch computation uses two calls. The library argument is the complete
library source string. The selected book names follow selection order.
Statement and aid sources use the source maps described above.

| Call | Result |
|---|---|

The preparation and assembly calls can return a failure. An `unproved`
result produces a skip entry with the reason `unproved`. The caller supplies the library
build carried out by the H4 interface and supplies file and checker operations
outside the logic.

`(h4-book-run-find-proof-with-templates p statement measures hints models
printing ordering conversions book-functions tables)` takes the template
tables of `book-tactics.md` and returns the same result as
`h4-book-run-find-proof-with-context`.
