# Statement generation

`lib` is the Library used by `BookProof`. A statement has a word string
`word` and a list of parsed fields `data` in the format of the statement
reader.
`name` is a prover symbol. `calls` contains the Calls described in
`prover/sig/termination.md`, in source order. `formulas` maps a formula to
the name of the first fact admitted for it. `aids` maps function names
to measure terms. These maps are association lists in insertion order.
`facts` is the FactIndex used by the search book.

| Function | Result | Failure |
|---|---|---|
| `(b1-generate-admit lib word data formulas)` | `(cons lib formulas)` with the resulting Library and first-name map. Only `define`, `theorem`, `axiom`, and a `constrain` with formulas add anything. | A failure from unpacking the fields or admitting a definition. |
| `(b1-generate-obligations word data)` | `(name calls)` for the obligation. Theorems and constraints have `nil` in the calls field. `(nil nil)` means there is no obligation. | A failure from reading the fields or finding recursive calls. |
| `(b1-generate-prove lib word data name calls aids formulas facts)` | `(cons entry lib)` with the proof entry and the resulting Library. An entry is `(word name counts source)` as in `prover/sig/proof.md`. | `unproved` for an unsupported obligation or a failure from the selected proof method or entry writer. |

The line lists contain strings with their final line feeds. Sets are lists
retaining the order supplied by the
caller and appending new members in discovery order. In particular,
`required-entries` adds emitted names in reverse entry order while
returning entries in forward order.

A Certificate is `(:b1-certificate context steps source entries facts definitions)`.
`context` is the set of prior raw lines. `steps` is an integer and `source`
is the entry proof text. `entries` is in Library order. `facts` and
`definitions` are maps of auxiliary names to clauses and definitions.
The cache maps raw statement lines to lists of Certificates in the
order they were stored. Pass `nil` for an empty cache. Certificates are
supplied and returned because reuse can select proofs from a subset of
the current statement context.

Pass `:none` for an omitted cache. A newly stored Certificate lists its
fact keys in order of first occurrence in `entries` and its definition
keys in the same order restricted to definitions. Installing a supplied
Certificate uses the supplied order of its two maps.
