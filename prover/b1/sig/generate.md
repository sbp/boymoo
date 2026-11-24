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
| `(b1-generate-prove lib word data name calls aids formulas facts)` | `(cons entry lib)` with the proof entry and the resulting Library. An entry is `(word name counts source)` as in `prover/sig/proof.md`. | `Unproved` for an unsupported obligation or a failure from the selected proof method or entry writer. |
| `(b1-generate-required-entries entries emitted proof)` | `(cons entries emitted)` with the selected entries in Library order and the resulting set of emitted names. `proof` is the proof text string. | A failure from writing a name or unpacking an entry. |
| `(b1-generate-measures-from-aids aid-lines)` | The measure map from `O<` measure lines in `aid-lines`. | A failure from parsing or unpacking a measure line. |
| `(b1-generate-initial-world library-lines)` | A world `(lib lines formulas)` built from the ground theory and the supplied library statement lines. `lines` records each distinct raw line. | A failure from building the library, reading the lines, or admitting their statements. |
| `(b1-generate-certificate-install certificate lib context auxiliaries)` | `(installed-p lib auxiliaries)` with the resulting Library and auxiliary-name set. On refusal the supplied Library and set are returned with `nil`. | A failure from reading an entry. |
| `(b1-generate-generate book count world cache statement-lines aid-lines)` | `(cons (list rows source) cache)` with the row list, complete proof text string, and resulting cache. `book` is the input name string and `count` is the expected number of obligation rows. Each row is `(book index word name status steps size reason)` with string fields. | A failure for a mismatched count or from reading, admission, or proof generation. An obligation that returns `Unproved` or `SearchBudgetExhausted` gives a skip row. |

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
