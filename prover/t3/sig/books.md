# Book statements and proof fragments

`lib` is a book proof context from `prover/t3/sig/book-values.md`. `search`
is the theorem index from `prover/t3/sig/book-theorems.md`. A statement
has a string `kind` and a list of frozen `data` fields. A record has the
form `(raw kind data)`, where `raw` is the source line including its line
terminator. An entry has the form in `prover/sig/library.md`. A measure
map is an association list of `(function-name . measure)` entries in
first-assignment order.

A Fragment has the form `(:t3-fragment entries facts packages reason)`.
`entries` is the list of needed auxiliary entries followed by the proof
entry, or a singleton skip entry on failure. `facts` maps names to
clauses and `packages` maps package-name strings to `(visible imports)`
pairs. Imports are the distinct imported names in the package table's
insertion order. The maps in a generated Fragment visit distinct keys
in their first-use order in the entry text. `reason` is empty on success
and gives the result label for a skipped obligation.

| Call | Result | Failure |
|---|---|---|
| `(t3-books-obligation kind data)` | The symbol that names the obligation, or `nil`. For a definition, the first recursive call suffices. | A failure from inspecting a statement or walking its terms. |
| `(t3-books-choice data)` | The choice fact's formula for the five fields of a `choose` statement. | A failure from accessing fields or substituting a term. |
| `(t3-books-admit lib kind data)` | The Library after its declaration and ordinary statement admission, then recording any choice fact. | A failure from declaration, admission or choice construction. |
| `(t3-books-step-arguments entries pattern)` | The list of frozen first arguments of matching proof-step lines, in entry order and then source order. The patterns are `*t3-books-fact-line*` and `*t3-books-compute-line*`. | A failure from parsing a matching line or reading its first argument. |
| `(t3-books-package-state lib package)` | The Boolean visibility and list of table values for the package-name string `package`, as a two-element list. | None on a book proof context. |
| `(t3-books-used-packages entries)` | The package-name strings mentioned in package computations, in proof-step order and with repeats retained. | A failure from reading the relevant terms or proof-step lines. |
| `(t3-books-fragment-init entries facts packages reason)` | A Fragment with the given fields. Use the empty string for the default reason. | None. |
| `(t3-books-fragment-entries fragment)` | The ordered entry list. | None. |
| `(t3-books-theorem-proof lib search name formula)` | `(cons entry lib)` for the first proof from the chosen tactic and theorem search, with the Library containing any new auxiliary entries. | A failure from the tactic, theorem search, or discarding failed entries. |
| `(t3-books-constrain-proof lib search declarations formulas)` | `(cons entry lib)` for the first witness proof, with the Library containing any new auxiliary entries. | A failure from the evaluator, witness recipes, search, or discarding failed entries. |
| `(t3-books-generate lib search kind name data measures)` | The proof Fragment. An `unproved` or `unsupported` result, or a shared `value` failure, becomes a skip with the reason `unproved`. The caller keeps its original `lib` and `search` for later obligations. | Other failures from proof construction, dependency extraction or discarding entries. |

The imports in a package-state value are full prover symbol datums. The
batch and fragment generators take a theorem index for the supplied
book proof context and pass its Library to the proof recipes.
The batch constructs the index from `base`. The fragment generator takes
the index in its `search` argument.

The first-call search in `t3-books-obligation` has an initial allowance of
1000000 and can return a `fuel` failure when that allowance is exhausted.
