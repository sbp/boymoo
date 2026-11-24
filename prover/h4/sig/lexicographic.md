# Lexicographic ordinal embedding

Terms and Steps use the forms in `prover/sig/proof.md`. A library has the
form in `prover/sig/library.md` and supplies the proof methods for the
embedding.

An Embedding has the form
`(:h4-embedding library leading list-ordinal ordinal fix-type list-order order)`.
The six fields after the library are the names of the corresponding local
lemmas, in the order in which the constructor adds them. The accessors
`h4-lexicographic-embedding-p`, `h4-lexicographic-embedding-leading`,
`h4-lexicographic-embedding-list-ordinal`,
`h4-lexicographic-embedding-ordinal`,
`h4-lexicographic-embedding-fix-type`,
`h4-lexicographic-embedding-list-order`, and
`h4-lexicographic-embedding-order` each take the Embedding and return the
indicated field without a failure. Use
`(h4-lexicographic-embedding-with-p embedding library)` to supply a
library with further facts. It returns an Embedding with that library
and the given lemma names.

Each function in the table can return a failure in place of its result,
except `natural-list-type`. An optional sequence uses `nil` when absent.
The optional `y` in `fact` uses `:none` for an absent operand. Pass
`*h4-lexicographic-list-ordinal*` as the default head in `encoding`.

| Function | Arguments in order | Result |
|---|---|---|
| `h4-lexicographic-natural-list-type` | Value term | Natural or natural-list type term |
| `h4-lexicographic-distinct` | Library, strict comparison Step, integer evidence Step list | Step proving the operands distinct |
| `h4-lexicographic-reverse-distinct` | Library, disequality Step | Step reversing the disequality |
| `h4-lexicographic-constructor` | Library, redex term | Constructor selector equation Step, or `nil` |
| `h4-lexicographic-cons-fact` | Library, cons construction term | Step proving the construction a cons |
| `h4-lexicographic-select-definition` | Library, call term, condition Step | Equality Step selecting a branch of the unfolded definition |
| `h4-lexicographic-define-list-ordinal` | Library | Library extended by the list ordinal definition and its measure proof |
| `h4-lexicographic-embedding-init` | Library | Embedding whose library includes the definitions and local lemmas |
| `h4-lexicographic-embedding-fact` | Embedding, lemma name, term `x`, term `y` or `:none` | Lemma instance Step |
| `h4-lexicographic-embedding-encoding` | Embedding, shape Step, function head | Equation Step for the encoding on that shape |
| `h4-lexicographic-embedding-cons-encodings` | Embedding, shape Step list | Two-element list of the encoding Steps and the cons evidence Steps in encoding and node order |
| `h4-lexicographic-embedding-normalize-selectors` | Embedding, term, evidence Step list, rewrite Step list | Equality Step for selector normalization |
| `h4-lexicographic-embedding-ordinal-proposition` | Embedding, formula term, evidence Step list, rewrite Step list | Step proving the ordinal formula |
| `h4-lexicographic-embedding-leading-exponent` | Embedding | Pair of the leading exponent lemma name and the Embedding with the extended library |
| `h4-lexicographic-embedding-positive-successor` | Embedding, number term | Two-element list of Steps for the positive successor and integer type |
| `h4-lexicographic-embedding-length-positive` | Embedding, cons Step | Step proving the list length positive |
| `h4-lexicographic-embedding-ordinal-on-lists` | Embedding | Pair of the list ordinality lemma name and the Embedding with the extended library |
| `h4-lexicographic-embedding-ordinal-on-values` | Embedding | Pair of the value ordinality lemma name and the Embedding with the extended library |
| `h4-lexicographic-embedding-acl2-nfix` | Embedding, term | Equality Step for the two natural fixers |
| `h4-lexicographic-embedding-fixed-types` | Embedding | Pair of the fixer type lemma name and the Embedding with the extended library |
| `h4-lexicographic-embedding-length-cancellation` | Embedding, length equality Step, cons Step for X, cons Step for Y | Equality Step for the tail lengths |
| `h4-lexicographic-embedding-coefficient-order` | Embedding, strict comparison Step, natural type Steps for X and Y | Strict comparison Step for the ordinal coefficients |
| `h4-lexicographic-embedding-order-on-lists` | Embedding | Pair of the list order lemma name and the Embedding with the extended library |
| `h4-lexicographic-embedding-order-on-values` | Embedding | Pair of the value order lemma name and the Embedding with the extended library |
| `h4-lexicographic-embedding-fixed-ordinal-order` | Embedding, comparison Step for fixed values | Step proving the order of their ordinal encodings |

The constants are `*h4-lexicographic-list-ordinal*`,
`*h4-lexicographic-lex-ordinal*`, `*h4-lexicographic-lex-fix*`,
`*h4-lexicographic-nat-list*`, `*h4-lexicographic-nfix-list*`,
`*h4-lexicographic-acl2-nfix*`, `*h4-lexicographic-first-expt*`,
`*h4-lexicographic-first-coeff*`, `*h4-lexicographic-rest-ord*`,
`*h4-lexicographic-posp*`, `*h4-lexicographic-d-less*`,
`*h4-lexicographic-l-less*`, `*h4-lexicographic-num-equal*`, and
`*h4-lexicographic-selector-definitions*`.
