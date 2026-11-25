# Proof normalization and signed branch tests

The proof operations take a Library as their first argument. Use the
Library representation and accessors in `prover/sig/library.md`. Terms and
Steps use the forms in `prover/sig/proof.md`.

`evidence` in a library proof operation is a list of Steps. `definitions`
is a list of symbol terms to unfold, in the given order. `tests` is a list
of two-element `(term holds)` lists with `t` for a true test and `nil`
for a false test. Omitted sequence arguments are `nil`.

| Call | Result | Failure |
|---|---|---|
| `(t3-logic-libraryproofs-constant lib term)` | A Step computing the value of the term, or `nil`. | A failure from reading a term or constructing a proof. |
| `(t3-logic-libraryproofs-natural lib term)` | A Step proving that the term is natural. | A failure from proof construction. |
| `(t3-logic-libraryproofs-type-of lib term evidence)` | A Step proving that the term is integer. | A failure from proof construction. |
| `(t3-logic-libraryproofs-normalize lib term evidence definitions)` | The simplification Step, or `nil`, unfolding wrapper symbols as well as the given definitions. | A failure from proof construction. |
| `(t3-logic-libraryproofs-by-value-leaves lib value tests)` | The list of `(value tests)` requests in true-branch-first traversal order, opening wrappers and lambda applications. | A failure from proof construction. |
| `(t3-logic-libraryproofs-by-value lib value template leaf tests)` | A Step proving the template instantiated at the given value. `leaf` is an alist of `((value tests) . result)` entries, with a Step or a failure for each request. | A construction failure or the failure from a leaf when visited. |
| `(t3-logic-libraryproofs-prove-formula lib term definitions evidence)` | The Step proving the formula using the evidence and definitions. | `unsupported` if no formula proof can be found, or a construction failure. |
| `(t3-logic-libraryproofs-required-entries lib source)` | Auxiliary entry records needed by the source string, in Library entry order. | A failure from writing an entry name. |
| `(t3-logic-libraryproofs-discard-entries lib start)` | The Library with the entries in the slice starting at integer `start` removed, together with their facts and definitions. | A failure for missing facts or definitions. |

The symbol constants are `*t3-logic-atom*`, `*t3-logic-consp*`,
`*t3-logic-endp*`, `*t3-logic-length*`, `*t3-logic-the-check*`,
`*t3-logic-zp*`, `*t3-logic-zpf*`, `*t3-logic-reciprocal*` and
`*t3-logic-legal-constantp*`. `*t3-logic-wrappers*` and
`*t3-logic-ppr-predicates*` list their symbol terms in proof order.

## Evidence

Evidence has the form `(:t3-evidence lib tests facts definitions expanded)`.
`facts` is an alist of `(first-literal . step)` entries in insertion order.
An existing key keeps its position when assigned a new Step.
`expanded` is a Boolean recording whether the signed tests have been expanded.
Use the constructor and accessors to work with Evidence.

| Call | Result | Failure |
|---|---|---|
| `(t3-logic-evidence-init lib tests extra definitions)` | Evidence with the given Library and signed tests. The initial fact values are the Steps in `extra`, assigned in order. The built-in expansion definitions precede the supplied definitions. | A failure from reading a Step. |
| `(t3-logic-evidence-lib evidence)` | The Library. | None. |
| `(t3-logic-evidence-tests evidence)` | The signed tests. | None. |
| `(t3-logic-evidence-facts evidence)` | The fact alist. | None. |
| `(t3-logic-evidence-definitions evidence)` | The expansion definitions, including the built-in prefix. | None. |
| `(t3-logic-evidence-expanded evidence)` | Whether the signed tests have been expanded. | None. |
| `(t3-logic-evidence-with-facts evidence facts)` | Evidence with the supplied fact alist. | None. |
| `(t3-logic-evidence-with-lib evidence lib)` | Evidence with the supplied Library. | None. |
| `(t3-logic-evidence-find evidence term)` | `(cons step evidence)` with the Step proving the term, or `nil` in its place, and the resulting Evidence. | A failure from proof construction. |
| `(t3-logic-evidence-require evidence term)` | `(cons step evidence)` with the Step proving the term and the resulting Evidence. | `unsupported` if the fact is missing, or a construction failure. |
| `(t3-logic-evidence-expand evidence)` | Evidence after processing all signed tests in order. | A failure from proof construction. |
| `(t3-logic-evidence-record evidence term holds proof)` | Evidence with the established fact and facts derived from it. `proof` is a Step. | A failure from proof construction. |
| `(t3-logic-evidence-positive-consp evidence term)` | A Step proving that the term is a cons, or `nil`. | A failure from proof construction. |
| `(t3-logic-evidence-integer evidence term)` | `(cons step evidence)` with the integrality Step and the resulting Evidence. | A failure from proof construction. |
| `(t3-logic-evidence-nonnegative evidence term)` | `(cons step evidence)` with the nonnegativity Step and the resulting Evidence. | A failure from proof construction. |

Each failure is returned as the entire result. The formula solver uses
the kind `unsupported` when it cannot establish a result.

## Simplification and type proofs

| Call | Result |
|---|---|
| `(t3-logic-libraryproofs-simplify lib term evidence definitions)` | An equality Step for the simplification, `nil` if there is none, or a failure. |
| `(t3-logic-libraryproofs-simplify-first lib step evidence definitions)` | The Step after simplifying its first literal, or a failure. |
| `(t3-logic-libraryproofs-prove lib term evidence definitions)` | A Step proving the term, or a failure. |
| `(t3-logic-libraryproofs-rational lib term evidence)` | A Step proving the term rational from its integrality, or a failure. |
| `(t3-logic-libraryproofs-number lib term evidence)` | A Step proving that the term is an ACL2 number, or a failure. |

`(t3-logic-libraryproofs-for-book lib)` returns a Library with the proof
dispatch tag `:t3-book`. Its natural and integer proofs use the book
rules for `SELF-NFIX` and `NFIX`, including in recursive
arithmetic and conditional proofs. A book proof context can keep its
package state in the fields specified in `prover/t3/sig/book-values.md`.

## Traversal and tokenization

| Call | Result | Failure |
|---|---|---|
| `(t3-logic-by-value-unfold proof value)` | An equality Step opening a wrapper or lambda application in `value`, or `nil` when neither applies. `proof` is a Proof. | A failure from proof construction. |
| `(t3-logic-by-value-check-leaf step value template)` | The Step when its first literal matches `template` instantiated with `value`. | A failure from reading the Step, substitution, or a mismatched literal. |
| `(t3-logic-token-plain-end source size index)` | The first offset at or after `index` outside the run of plain symbol characters. | None on the given byte offsets. |
| `(t3-logic-token-end source size index plain-end)` | The first offset after the token beginning at `index`, or `nil` if no token begins there. `plain-end` is the result of `t3-logic-token-plain-end`. | None on the given byte offsets. |

The tokenization calls take a proof-text string. `size` is its length
and `index` is a nonnegative offset below
`size`. Tokens match quoted string contents or qualified symbol names.
