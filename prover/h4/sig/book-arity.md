# List lengths and arities

Terms, Steps and Libraries have the forms in `prover/sig/proof.md` and
`prover/sig/library.md`. `p` is the Library used by H4 tactics. These recipes
return Steps without adding entries to `p`. A `shape` argument is a Step
whose first literal asserts or denies the indicated `CONSP` test. `size` is
the integer width of a list shape. A recognizer returns `nil` when it finds no
match. Every pair of terms returned by a recognizer is a two-element list.

The prover symbol constants are `*h4-book-arity-take*`,
`*h4-book-arity-pairlis*`, `*h4-book-arity-apply*`,
`*h4-book-arity-apply-lambda*`, `*h4-book-arity-formals*`,
`*h4-book-arity-body*`, `*h4-book-arity-primitive*`,
`*h4-book-arity-primitivep*`, `*h4-book-arity-lamb*`,
`*h4-book-arity-checked-badge*`, `*h4-book-arity-tame-arguments*`,
`*h4-book-arity-badge*`, `*h4-book-arity-primitive-badge*` and
`*h4-book-arity-user-badge*`.

| ACL2 call | Arguments and result | Failure |
|---|---|---|
| `(h4-book-arity-length-shape term size)` | The nested shape test for a list term of the given width. | A failure for a negative or noninteger width. |
| `(h4-book-arity-length-positive p term shape)` | A Step proving the length of the cons term is positive. | A failure from proof construction. |
| `(h4-book-arity-predecessor-length p term shape)` | A Step equating the predecessor of the term's length with the length of its tail. | A failure from proof construction. |
| `(h4-book-arity-length-equals p term size)` | A Step equating the length test for `size` with its corresponding shape test. | A failure from constructing the shape or proof. |
| `(h4-book-arity-length-test formula)` | `(term width)` for an equality between a length test and its shape test, or `nil`. | A failure from reading a malformed formula. |
| `(h4-book-arity-fixed-prefix p formula sequence values)` | A Step proving the given `PAIRLIS$` formula for the parallel sequence and values terms. | A failure from proof construction. |
| `(h4-book-arity-prefix-shape formula)` | The terms `(sequence values)` in a matching `PAIRLIS$` formula, or `nil`. | A failure from reading a malformed formula. |
| `(h4-book-arity-checked-length-shape formula)` | The three-argument arity check call in a matching implication, or `nil`. | A failure from reading a malformed formula. |
| `(h4-book-arity-checked-length p formula call)` | The induction Step proving the length implication for the given arity check call. | A failure from proof construction. |
| `(h4-book-arity-lambda-formals p function shape)` | A Step equating the formals of a lambda object with the head of its tail. | A failure from proof construction. |
| `(h4-book-arity-lambda-application p mode formula)` | A Step for the given application mode and formula, or `nil` for an unrecognized mode. | A failure from proof construction. |
| `(h4-book-arity-badge-properties p formula)` | A Step proving the badge field implication. | A failure from proof construction. |
| `(h4-book-arity-length-type p term)` | A Step proving a `LENGTH` call returns a natural number. | A failure from proof construction. |
| `(h4-book-arity-tame-list-type p formula)` | A Step proving the true list implication for a tame cons term. | A failure from proof construction. |
| `(h4-book-arity-badge-type p formula)` | A Step proving the conditional badge type formula. | A failure from proof construction. |
| `(h4-book-arity-symbol-arity p formula)` | A Step proving the application formula for a symbol with arity one. | A failure from proof construction. |
| `(h4-book-arity-arity-mode formula)` | A string naming the application or badge pattern, or `nil`. | A failure from reading a malformed formula. |
| `(h4-book-arity-arity-proof p formula)` | A Step for the first applicable recipe, or `nil`. | A failure from proof construction. The checked-length attempt advances to another mode for the fallback kinds in `prover/h4/notes/failures.md`. |
