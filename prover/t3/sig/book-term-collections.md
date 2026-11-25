# Types of term collections

`lib` is a Library with the T3 proof rules. Terms, names and Steps use the
forms in `prover/sig/proof.md`. `formula` is a theorem's formula and `name`
is its symbol. An entry is `(kind name counts source)` as in
`prover/sig/library.md`. Each function can return a failure as its entire result.

| Call | Result |
|---|---|
| `(t3-book-term-collections-append-lists lib)` | Library with the pseudo-term-list lemma for append. |
| `(t3-book-term-collections-leaf-types lib name formula)` | `(cons entry lib)` with the theorem entry and the Library including the append lemma. |
| `(t3-book-term-collections-constructed-type n lib predicate value known)` | Step for `(predicate value)`, using `known`, an ordered list of Steps. Start with natural-number fuel `1000000`. Returns `unsupported` for an unrecognized constructor, `fuel` on exhaustion, or a failure from constructing the proof. |
| `(t3-book-term-collections-aligned-types lib operation)` | Step proving type preservation of the binary list traversal named by the symbol `operation`. |
| `(t3-book-term-collections-typed-conjunction lib)` | Library with the binary and list conjunction lemmas in that order. |
| `(t3-book-term-collections-equality-types lib name formula)` | `(cons entry lib)` with the theorem entry and the Library including the aligned-equality lemma and any conjunction lemmas. |

The prover symbols are `*t3-book-term-collections-if-leaves*`,
`*t3-book-term-collections-conjoin*`, `*t3-book-term-collections-conjoin2*`,
and `*t3-book-term-collections-equalities*`. The append lemma label is
`*t3-book-term-collections-append-type*`, a string. In `leaf-types`, the
substitutions used for induction are ordered by first encounter of the
selected subterm, traversing true branches before false branches and append
arguments from left to right.

`(t3-book-term-collections-step-term-at step index)` reads a zero-based
index in the Step's first literal. It can return a failure from reading the
Step or the term.

The by-value traversal used by collection and name proofs offers the
following calls. A leaf request has the form
`(:t3-book-term-collections-leaf value tests stack)`. Its stack records the
pending proof operations. Keep the stack with the request through the call
to `by-value-resume`.

| Call | Result |
|---|---|
| `(t3-book-term-collections-by-value-start lib value tests)` | The first leaf request for the given term and ordered signed-test list, or a failure. |
| `(t3-book-term-collections-by-value-resume lib template request step)` | The next leaf request, the Step for `template` at the original term, or a failure. `step` proves `template` at the requested leaf value. The slot in `template` is `*proof-result*`. |

For the Library of a book proof context, use the `:t3-book` Proof dispatch tag
specified in `prover/t3/sig/logic.md`. It selects the book proof context rules for
normalizing the constructors.
