# `book-proofs.lisp`

The arguments `lib`, `index`, `rulers` and `goal` use the Library, FactIndex, Rulers and term forms of their owners. All functions in the table can return a failure in place of their result. Functions returning `(cons value lib)` give the value and the library after the call. A missing optional proof is `nil` within the pair.

| Function | Arguments in order | Result |
|---|---|---|
| `run-helper-names` | Entry source string | Occurrences of auxiliary names beginning with `ACL2::SELF-` or `ACL2::T1-`, in order. |
| `run-entry-names` | Entry | The list of symbols declared by the entry. |
| `run-required-entries` | Auxiliary entry list, last entry | The selected entries in source order, including the last entry. |
| `run-add-statement` | `lib`, the kind string, parsed statement fields | The library with the statement's definitions or facts. |
| `book-proofs-obligation-name` | Kind string, parsed statement fields | Name of the obligation, or `nil`. |
| `book-proofs-certificate` | `lib`, the last entry | The certificate with the required entries and external facts. |
| `book-proofs-cons-from-guard` | `lib`, the base term, `rulers`, `index` | A Step for the base being a cons, or `nil`. |
| `book-proofs-book-termination` | `lib`, parsed definition fields, the stored measure alist, `index` | `(cons entry lib)` for the measure entry. |
| `book-proofs-book-prover-prove` | `lib`, the kind string, parsed statement fields, the obligation name, the stored measure alist, `index` | `(cons certificate lib)`. An unproved obligation produces a skip certificate with the original library and the failure kind as its reason. |

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
