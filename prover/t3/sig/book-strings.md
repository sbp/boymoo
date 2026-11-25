# String results

`lib` is a Library as in `prover/sig/library.md`. Terms and Steps use the
forms in `prover/sig/proof.md`. `tests` is the ordered list of `(term holds)`
pairs, `holds` being Boolean. `trail` is the ordered list of function symbols
whose definitions have been opened. Use `nil` for omitted tests or trail.

A string proof context has the form `(:t3-string-results lib earlier)`.
Use `t3-book-strings-string-results-init` to construct it and
`t3-book-strings-string-results-lib` and
`t3-book-strings-string-results-earlier` to read its fields.

`earlier` is a callback represented by an alist of `(formula . result)`
entries. A result is a Step, `nil` for no proof, or a failure. When the next
formula is absent, the tactic returns `(:t3-book-strings-earlier formula)`.
Supply the result in `earlier` and call again with the same inputs. Entries
may be supplied in request order.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t3-book-strings-string-results-init lib earlier)` | StringResults object for the Library and earlier-proof callback. | None. |

`(t3-book-strings-earlier-request-p result)` recognizes an earlier-proof
request.
