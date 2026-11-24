# `book-proofs.lisp`

An entry is `(kind name counts source)`, with a kind string, a prover symbol, a list of step counts, and the source string. A `Certificate` has the form `(:certificate entries requirements reason)`. The entries are in source order. The requirements are an insertion-ordered alist from fact names to clauses, and the reason is a string, empty for a proof. `book-proofs-make-certificate` takes those three fields. `book-proofs-certificate-entries`, `book-proofs-certificate-requirements` and `book-proofs-certificate-reason` take a certificate and return the named field. These functions do not return a failure.

The arguments `lib`, `index`, `rulers` and `goal` use the Library, FactIndex, Rulers and term forms of their owners. All functions in the table can return a failure in place of their result. Functions returning `(cons value lib)` give the value and the library after the call. A missing optional proof is `nil` within the pair.

| Function | Arguments in order | Result |
|---|---|---|
| `run-helper-names` | Entry source string | Occurrences of auxiliary names beginning with `ACL2::SELF-` or `ACL2::T1-`, in order. |
| `run-entry-names` | Entry | The list of symbols declared by the entry. |
| `run-required-entries` | Auxiliary entry list, last entry | The selected entries in source order, including the last entry. |
| `run-add-statement` | `lib`, the kind string, parsed statement fields | The library with the statement's definitions or facts. |
| `run-quoted-input` | Byte string | The bytes written as a quoted string term. |
| `book-proofs-obligation-name` | Kind string, parsed statement fields | Name of the obligation, or `nil`. |
| `book-proofs-certificate` | `lib`, the last entry | The certificate with the required entries and external facts. |
| `book-proofs-earlier-decrease` | `lib`, `goal`, `rulers`, `index` | `(cons step lib)` for the first applicable descent proof. |
| `book-proofs-cons-from-guard` | `lib`, the base term, `rulers`, `index` | A Step for the base being a cons, or `nil`. |
| `book-proofs-wrapped-selector-decrease` | `lib`, `goal`, `rulers`, `index` | `(cons step lib)` for a decrease after reducing the selector expression. |
| `book-proofs-conditional-count-decrease` | `lib`, `goal`, `rulers` | `(cons step lib)` for a conditional count decrease. |
| `book-proofs-book-termination` | `lib`, parsed definition fields, the stored measure alist, `index` | `(cons entry lib)` for the measure entry. |
| `book-proofs-book-prover-prove` | `lib`, the kind string, parsed statement fields, the obligation name, the stored measure alist, `index` | `(cons certificate lib)`. An unproved obligation produces a skip certificate with the original library and the failure kind as its reason. |

A BookProver holds the base library, the set of base lines, the base
measure alist, skipped lines by input name, and the sets of proved and
seen lines. `book-proofs-book-prover-init` constructs it from the base
statement lines and measure lines. `book-proofs-book-prover-statement`
returns `(kind data)` for an input line.
`book-proofs-book-prover-find-certificate` has the arguments and result
of `book-proofs-book-prover-prove`.
`book-proofs-book-prover-generate` takes a BookProver, an input name,
raw statement lines and raw aid lines. It returns `(cons rows prover)`,
with rows of the form `(number kind name certificate)` and the resulting
BookProver. These functions may propagate a failure.

The concrete BookProver form is `(:book-prover base library-lines library-measures skipped-by-book distinct-proved distinct-seen)`. `book-proofs-make-book-prover` takes the six fields. The accessors are `book-proofs-book-prover-base`, `book-proofs-book-prover-library-lines`, `book-proofs-book-prover-library-measures`, `book-proofs-book-prover-skipped-by-book`, `book-proofs-book-prover-distinct-proved` and `book-proofs-book-prover-distinct-seen`. Each takes a BookProver and does not return a failure.

`book-proofs-cons-from-guard` pairs its Step or `nil` with the resulting
library. A library pair can carry a failure in the value position so
the caller can use the resulting library.

| Shared call | Result |
|---|---|
| `(run-parse-line raw)` | A string without its line terminator becomes `(kind fields)`, or a reader failure. |
| `(run-split-byte-lines source)` | The lines of the string split at CR and LF line boundaries. |
| `(run-definition-names definitions)` | First field of each definition in order, or a failure on a missing field. |
| `(run-statement-fact-names kind data)` | Names of facts a parsed statement makes available, in statement order, or a failure on a missing field. |
| `(run-index-names index names)` | Index after adding the supplied fact names in sequence, or a failure. The index already holds their library. |
| `(book-proofs-let* bindings body)` | Abbreviation for sequential bindings that return the first failure in place of the body. |
