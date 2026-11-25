# List type preservation

`library` is the Library component of BookLogic, as described in `prover/sig/library.md`. `recursive` is the set of recursive function symbols as a list without repeats. Only membership in this set is tested. Steps and terms have the forms in `prover/sig/proof.md`. `evidence` is an Evidence object from `prover/t4/sig/structural.md`.

The four theorem tactics return `(cons step library)` on success or `(cons nil library)` when the tactic does not apply. The library in the result includes the entries added during the attempt. Each tactic can return a failure. The `replies` argument for the calls below supplies the results of methods of BookLogic and any external leaf function.

| ACL2 call | Result |
|---|---|
| `(t4-list-types-cdr-path value object)` | Boolean. True when stripping one or more `CDR` applications from `value` yields `object`. May return a failure on a malformed application. |
| `(t4-list-types-in-first library step equality)` | Tidied Step with the first argument of its first literal rewritten by `equality`. May return a failure. |

The constants `*t4-list-types-eq*`, `*t4-list-types-endp*`, `*t4-list-types-acons*`, `*t4-list-types-append*`, and `*t4-list-types-double*` are the prover symbols `EQ`, `ENDP`, `ACONS`, `BINARY-APPEND`, and `DOUBLE-REWRITE`, respectively.

## Method requests

| Operation | Arguments in order | Value |
|---|---|---|
| `:use-arithmetic` | None | `nil` after BookLogic installs its arithmetic lemmas. |
| `:known` | Term, Evidence | Step for known evidence, or `nil`. |
| `:fact-proof` | Term, Evidence | Step from an indexed fact, or `nil`. |
| `:equation` | Term, Evidence | Equality Step for the term, or `nil`. |
| `:nested` | Predicate symbol, value term, Evidence | Step for the predicate of the value, obtained by calling the supplied leaf function. |

## Ordered replies

`:prove` takes a term, an ordered list of evidence Steps, and an ordered
list of definitions. It calls BookLogic's proof operation and
returns the resulting Step or failure. This operation has no Evidence
object as an argument. An ordered reply is `(cons step library)` or
`(cons failure library)`. A keyed reply is `(list step library nil)` or
`(list failure library nil)`.
