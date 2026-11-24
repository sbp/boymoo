# Book proof dependencies and assembly

A proof entry is `(kind name counts source)` as in `prover/sig/library.md`. Its source is a byte string. Names in parsed statement data are frozen prover data as in `prover/sig/proof.md`.

| Function | Arguments and result | Failure |
|---|---|---|
| `(h3-books-statement-name kind data)` | The name of the first definition or constrained function, or the name of the theorem. Takes a statement kind string and its frozen fields. Returns `nil` for other kinds. | A failure when a required field cannot be read. |
| `(h3-books-proof-dependencies lib proof)` | Takes a Library and a proof entry. Returns `(prelude dependencies)`. The prelude contains all selected entries in the Library's entry order. Dependencies are `(name clause)` pairs in the order in which external facts were first encountered. | A failure from reading an entry, a missing external fact, or exhausted fuel. |
| `(h3-books-assemble book obligations omitted)` | Takes a book path string, a list of `(name proof prelude reason)` obligations and an ordered alist from omitted names to reason strings. A proof is an entry or `nil`; a prelude is an entry list. Returns `(source rows end-lines)` with the complete proof text, the tab-separated rows including their newlines, and the `(last-line name)` pairs, in obligation order. Local entries appear at their first use. | A failure when entries with the same local name have different headers, or when proof data cannot be written. |
| `(h3-books-proof-dependencies-include n name entries facts needed external)` | Includes the named entry and visits its proof. The name-to-entry and name-to-clause maps are alists. Returns `(needed external)` with the updated first-discovery name list and insertion-ordered external fact alist. | A failure from reading an entry, a missing entry or fact, or exhausted fuel. |
| `(h3-books-proof-dependencies-visit n entry entries facts needed external)` | Visits fact lines of one entry in source order with the same maps and state as `include`. Returns the two updated lists in the same form. | A failure from reading an entry, a missing fact, or exhausted fuel. |

Supply `1000000` for the initial fuel `n`. The proof cache, worklist and results files, checker process, and command-line runner are outside the logic book.
