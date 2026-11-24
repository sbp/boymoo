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
| `(t3-book-strings-string-results-string results value tests trail)` | Step for `STRINGP` of the value term, or an earlier-proof request. | `Unsupported` for an unresolved term, or a callback or construction failure. |
| `(t3-book-strings-string-results-return-cases results value tests trail)` | Step for `STRINGP` of the value term by return cases, or an earlier-proof request. | A callback or construction failure. |
| `(t3-book-strings-string-results-projected results value tests trail)` | Step for `STRINGP` of the selected result of a producer, or an earlier-proof request. `value` is the `MV-NTH` term. | `Unsupported` for an unresolved projection, or a callback or construction failure. |
| `(t3-book-strings-string-result lib formula earlier)` | Step for the formula, `nil` for a formula of another form, or an earlier-proof request. | A callback or construction failure, including `Unsupported`. |

`(t3-book-strings-earlier-request-p result)` recognizes an earlier-proof
request.
