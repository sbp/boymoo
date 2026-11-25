# A finite bound for variable-name search

`lib` is the Library used by the T3 proof routines. Terms and Steps have the
forms in `prover/sig/proof.md`. An Evidence object is the signed-test store of
`logic.lisp`. A failure is the entire result.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t3-genvar-package-name symbol)` | Term for the package name of term `symbol`. | None. |
| `(t3-genvar-package-imports witness)` | Term for the imports of the package of term `witness`. | None. |
| `(t3-genvar-genvar-measure formals)` | Gap measure for the four formals in witness, prefix, avoid-list, counter order. | A failure for an invalid sequence of formals. |
| `(t3-genvar-name-conditions symbol)` | List of the six conditions for the symbol term, in the order in which they are used as premises. | None. |
| `(t3-genvar-common-lisp-name-arm lib term path)` | `(openings body place)` for the Common Lisp name tests under `term`, or `nil` when there is no match. `path` and `place` are term argument index lists. Each opening is `(step path)` in outermost-first order. Pass `nil` for the initial path. | A failure from inspecting or opening a value. |
| `(t3-genvar-legal-name-equation lib)` | `(cons step lib)` with the rewritten legal-name definition equality and the Library containing the auxiliary name-tests definition. | `unsupported` if the Common Lisp branch does not match, or a failure from constructing or adding a proof. |
| `(t3-genvar-ordinary-variable-name lib)` | Library extended with the common name-tests definition and the ordinary variable name lemma. | A failure from constructing or adding a proof. |
| `(t3-genvar-capacity-of-generated-name lib characters lower counter nat-counter)` | Step bounding `counter` by the capacity of `characters`, an append term. `lower` is the decimal capacity bound Step and `nat-counter` establishes the natural counter. | A failure from inspecting or constructing a proof. |
| `(t3-genvar-symbol-name-equality lib candidate string witness stringp symbolp)` | Name equality Step for the candidate, using its definition equality Step, the string and witness terms, and the two type Steps. | A failure from inspecting or constructing a proof. |
| `(t3-genvar-prefix-observations lib chars string joined-cons coercion join)` | Two-element list of the first-character equality Step and the nonzero-length Step. `chars` and `string` are the list and string terms. The other arguments are the cons, coercion and append Steps. | A failure from inspecting or constructing a proof. |
| `(t3-genvar-legal-candidate lib witness prefix candidate-eq evidence joined string coercion name-eq no-import)` | Legal-variable Step using the guard Evidence, witness and prefix terms, the append and string terms, and the supplied equations and nonmembership Step. | A failure from missing evidence or proof construction. |
| `(t3-genvar-gap-from-list lib smaller larger counter nat-counter named below member chosen other first)` | Gap decrease Step. `smaller`, `larger`, `counter`, `chosen` and `other` are terms. `nat-counter`, `named`, `below` and `member` are Steps. `first` is true for the avoid-list case. | A failure for a mismatched gap, or a failure from proof construction. |
| `(t3-genvar-descent lib goal call)` | Decrease Step for the ordinal comparison term `goal` and recursive Call `call` from `termination.lisp`. | A failure from inspecting the call, missing evidence, a failed assertion, or proof construction. |
| `(t3-genvar-build lib)` | Library with the decimal capacity, name bounds, character-list append and ordinary name entries, in that order. | A failure from constructing or adding a proof. |

`*t3-genvar-genvar*`, `*t3-genvar-guard*`, `*t3-genvar-gsym*`,
`*t3-genvar-legal*`, `*t3-genvar-legal-name*`, `*t3-genvar-package*`,
`*t3-genvar-imports*`, `*t3-genvar-intern*`, `*t3-genvar-symbolp*`,
`*t3-genvar-char*`, `*t3-genvar-nth*` and `*t3-genvar-eql*` are term
symbols. `*t3-genvar-common-lisp*` and `*t3-genvar-keyword*` are quoted
package names. `*t3-genvar-star*` and `*t3-genvar-ampersand*` are quoted
characters.

The capacity bound and descent return `(cons step lib)`. The Library field
retains any scaling lemma added while bounding the generated name.
The legal-candidate proof returns `(cons step evidence)` with the resulting
Evidence.
