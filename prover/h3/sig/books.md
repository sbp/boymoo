# Book proof dependencies and assembly

A proof entry is `(kind name counts source)` as in `prover/sig/library.md`. Its source is a byte string. Names in parsed statement data are frozen prover data as in `prover/sig/proof.md`.

| Function | Arguments and result | Failure |
|---|---|---|
| `(h3-books-proof-dependencies-include n name entries facts needed external)` | Includes the named entry and visits its proof. The name-to-entry and name-to-clause maps are alists. Returns `(needed external)` with the updated first-discovery name list and insertion-ordered external fact alist. | A failure from reading an entry, a missing entry or fact, or exhausted fuel. |
| `(h3-books-proof-dependencies-visit n entry entries facts needed external)` | Visits fact lines of one entry in source order with the same maps and state as `include`. Returns the two updated lists in the same form. | A failure from reading an entry, a missing fact, or exhausted fuel. |

Supply `1000000` for the initial fuel `n`. The proof cache, worklist and results files, checker process, and command-line runner are outside the logic book.
